# Tests for the MoarVM dispatch mechanism

plan(119);

{
    sub const($x) {
        nqp::dispatch('boot-constant', $x)
    }

    ok(const(1) == 1, 'boot-constant on first call passes through the value');
    ok(const(2) == 1, 'boot-constant fixates the value');
}

{
    sub value($x) {
        nqp::dispatch('boot-value', $x)
    }

    ok(value(1) == 1, 'boot-value passes through value');
    ok(value(2) == 2, 'boot-value does not fixate value');
}

{
    sub code-constant($code) {
        nqp::dispatch('boot-code-constant', $code, 2, 3);
    }
    ok(code-constant(-> $x, $y { $x + $y }) == 5, 'boot-code-constant invokes bytecode with args');
    ok(code-constant(-> $x, $y { $x * $y }) == 5, 'boot-code-constant fixates the callee');
}

{
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'identity', -> $capture {
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-value', $capture);
    });
    ok(nqp::dispatch('identity', 42) == 42, 'Can define identity dispatch (1)');
    ok(nqp::dispatch('identity', 'foo') eq 'foo', 'Can define identity dispatch (2)');
    ok(nqp::dispatch('identity', 3.14) == 3.14, 'Can define identity dispatch (3)');
    ok(nqp::eqaddr(nqp::dispatch('identity', NQPMu), NQPMu), 'Can define identity dispatch (4)');

    nqp::dispatch('boot-syscall', 'dispatcher-register', 'wrap-identity', -> $capture {
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'identity', $capture);
    });
    ok(nqp::dispatch('wrap-identity', 101) == 101,
        'Chains of userspace dispatcher delegations work (1 deep)');

    nqp::dispatch('boot-syscall', 'dispatcher-register', 'wrap-wrap-identity', -> $capture {
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'wrap-identity', $capture);
    });
    ok(nqp::dispatch('wrap-wrap-identity', 666) == 666,
        'Chains of userspace dispatcher delegations work (2 deep)');
}

{
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'drop-first', -> $capture {
        my $capture-derived := nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-value', $capture-derived);
    });
    ok(nqp::dispatch('drop-first', 'first', 'second') eq 'second',
        'dispatcher-drop-arg works');

    nqp::dispatch('boot-syscall', 'dispatcher-register', 'drop-first-two', -> $capture {
        my $capture-da := nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0);
        my $capture-db := nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture-da, 0);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-value', $capture-db);
    });
    ok(nqp::dispatch('drop-first-two', 'first', 'second', 'third', 'fourth') eq 'third',
        'Multiple applications of dispatcher-drop-arg work');
}

{
    my $target := -> $x { $x + 1 }
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'call-on-target', -> $capture {
        my $capture-derived := nqp::dispatch('boot-syscall',
                'dispatcher-insert-arg-literal-obj', $capture, 0, $target);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                'boot-code-constant', $capture-derived);
    });
    sub cot() { nqp::dispatch('call-on-target', 49) }
    ok(cot() == 50,
        'dispatcher-insert-arg-literal-obj works at start of capture');
    ok(cot() == 50,
        'dispatcher-insert-arg-literal-obj works at start of capture after link too');
}

{
    my $target := -> $x, $y { $x ~ $y }
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'insert-world', -> $capture {
        my $capture-derived := nqp::dispatch('boot-syscall',
                'dispatcher-insert-arg-literal-str', $capture, 2, 'world');
        nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                'boot-code-constant', $capture-derived);
    });
    sub insert() { nqp::dispatch('insert-world', $target, 'hello ') }
    ok(insert() eq 'hello world',
        'dispatcher-insert-arg-literal-str works at end of capture');
    ok(insert() eq 'hello world',
        'dispatcher-insert-arg-literal-str works at end of capture after link too');
}

{
    my $adder := -> $x, $y { $x * $y }
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'dupe-arg', -> $capture {
        my $first-arg := nqp::dispatch('boot-syscall',
                'dispatcher-track-arg', $capture, 1);
        my $capture-derived := nqp::dispatch('boot-syscall',
                'dispatcher-insert-arg', $capture, 2, $first-arg);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                'boot-code-constant', $capture-derived);
    });
    sub dupe() { nqp::dispatch('dupe-arg', $adder, 3) }
    ok(dupe() == 9, 'Can duplicate an argument');
    ok(dupe() == 9, 'Argument duplicating works after link too');
}

{
    my class C1 { }
    my class C2 { }
    my class C3 { }
    my $count := 0;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'type-name', -> $capture {
        $count++;
        my $arg := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 0);
        my $arg-val := nqp::captureposarg($capture, 0);
        my str $name := $arg-val.HOW.name($arg-val);
        nqp::dispatch('boot-syscall', 'dispatcher-guard-type', $arg);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-constant',
            nqp::dispatch('boot-syscall', 'dispatcher-insert-arg-literal-str',
                nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0),
                0, $name));
    });
    sub type-name($obj) {
        nqp::dispatch('type-name', $obj)
    }

    ok(type-name(C1) eq 'C1', 'Dispatcher setting guard works');
    ok($count == 1, 'Dispatch callback ran once');
    ok(type-name(C1) eq 'C1', 'Can use it another time with the same type');
    ok($count == 1, 'Dispatch callback was not run again');

    ok(type-name(C2) eq 'C2', 'Can handle polymorphic sites when guard fails');
    ok($count == 2, 'Dispatch callback ran a second time for new type');
    ok(type-name(C2) eq 'C2', 'Second call with new type works');
    ok(type-name(C1) eq 'C1', 'Call with original type still works');
    ok($count == 2, 'Dispatch callback only ran a total of 2 times');

    ok(type-name(C3) eq 'C3', 'Can handle a third level of polymorphism');
    ok($count == 3, 'Dispatch callback ran a third time for new type');
    ok(type-name(C1) eq 'C1', 'Works with first type');
    ok(type-name(C2) eq 'C2', 'Works with second type');
    ok(type-name(C3) eq 'C3', 'Works with third type');
    ok($count == 3, 'There were no further dispatch callback invocations');
}

{
    my class C1 { }
    my class C2 { }
    my $count := 0;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'conc', -> $capture {
        $count++;
        my $arg := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 0);
        my $arg-val := nqp::captureposarg($capture, 0);
        my str $result := nqp::isconcrete($arg-val) ?? 'conc' !! 'type';
        nqp::dispatch('boot-syscall', 'dispatcher-guard-concreteness', $arg);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-constant',
            nqp::dispatch('boot-syscall', 'dispatcher-insert-arg-literal-str',
                nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0),
                0, $result));
    });
    sub conc($obj) {
        nqp::dispatch('conc', $obj)
    }

    ok(conc(C1) eq 'type', 'Concreteness guard test dispatcher works on type object');
    ok(conc(C1.new) eq 'conc', 'Concreteness guard test dispatcher works on instance');
    ok($count == 2, 'Ran once for each concreteness');
    ok(conc(C1) eq 'type', 'Repeated test works on type object');
    ok(conc(C1.new) eq 'conc', 'Repeated test works on instance');
    ok(conc(C2) eq 'type', 'Repeated test works on a different type object');
    ok(conc(C2.new) eq 'conc', 'Repeated test works on different instance');
    ok($count == 2, 'Was really only guarding concreteness');
}

{
    my class C { has $!foo; method foo() { $!foo } }
    my $count := 0;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'literal', -> $capture {
        $count++;
        my $arg := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 0);
        my $arg-val := nqp::captureposarg($capture, 0);
        nqp::dispatch('boot-syscall', 'dispatcher-guard-literal', $arg);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-constant',
            nqp::dispatch('boot-syscall', 'dispatcher-insert-arg-literal-obj',
                nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0),
                0, $arg-val.foo));
    });
    sub literal($obj) {
        nqp::dispatch('literal', $obj)
    }

    my $i1 := C.new(foo => 'bar');
    my $i2 := C.new(foo => 'baz');
    ok(literal($i1) eq 'bar', 'Literal guard test dispatcher works on instance 1');
    ok(literal($i2) eq 'baz', 'Literal guard test dispatcher works on instance 2');
    ok($count == 2, 'Ran once for each literal');
    ok(literal($i1) eq 'bar', 'Repeated literal guard test dispatcher works on instance 1');
    ok(literal($i2) eq 'baz', 'Repeated literal guard test dispatcher works on instance 2');
    ok($count == 2, 'Guards match with same literal');
}

{
    my class Nil { }
    my class C { }
    my class D { }
    my $count := 0;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'nil-check', -> $capture {
        $count++;
        my $arg := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 0);
        my $arg-val := nqp::captureposarg($capture, 0);
        my $is-nil := nqp::istype($arg-val, Nil);
        if $is-nil {
            nqp::dispatch('boot-syscall', 'dispatcher-guard-literal', $arg);
        }
        else {
            nqp::dispatch('boot-syscall', 'dispatcher-guard-not-literal-obj', $arg, Nil);
        }
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-constant',
            nqp::dispatch('boot-syscall', 'dispatcher-insert-arg-literal-str',
                nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0),
                0, $is-nil ?? 'nil' !! 'not nil'));
    });
    sub nil-check($obj) {
        nqp::dispatch('nil-check', $obj)
    }

    ok(nil-check(C) eq 'not nil', 'Can add not literal guard');
    ok(nil-check(C.new) eq 'not nil', 'Dispatch that is not that literal works');
    ok(nil-check(D.new) eq 'not nil', 'Dispatch on other type works');
    ok($count == 1, 'Ran dispatch only once since unwanted literal never passed');
    ok(nil-check(Nil) eq 'nil', 'Passing unwanted literal does not meet guard');
    ok($count == 2, 'Now dispatch was run twice');
    ok(nil-check(C) eq 'not nil', 'Another case without unwanted literal');
    ok(nil-check(Nil) eq 'nil', 'Another case with unwanted literal');
    ok($count == 2, 'No further dispatch runs');
}

{
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'dies', -> $capture {
        nqp::die('my dying dispatcher')
    });
    my $message := '';
    try {
        nqp::dispatch('dies', 42);
        CATCH {
            $message := ~$_;
        }
    }
    ok($message eq 'my dying dispatcher', 'Exceptions thrown in dispatch are passed along');
}

{
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'bad-dupe', -> $capture {
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-value', $capture);
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-value', $capture);
    });
    my $message := '';
    try {
        nqp::dispatch('bad-dupe', 42);
        CATCH {
            $message := ~$_;
        }
    }
    ok($message ~~ /'dispatcher-delegate'/, 'Decent error on dupe dispatcher-delegate');
}

{
    my class Wrapper {
        has $!value;
    }
    my class Subclass is Wrapper {
    }
    my $count := 0;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'read-value', -> $capture {
        $count++;
        my $arg := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 0);
        my $value := nqp::dispatch('boot-syscall', 'dispatcher-track-attr', $arg,
            Wrapper, '$!value');
        nqp::dispatch('boot-syscall', 'dispatcher-delegate', 'boot-value',
            nqp::dispatch('boot-syscall', 'dispatcher-insert-arg',
                nqp::dispatch('boot-syscall', 'dispatcher-drop-arg', $capture, 0),
                0, $value));
    });
    sub rv($obj) {
        nqp::dispatch('read-value', $obj)
    }
    ok(rv(Wrapper.new(value => 42)) == 42, 'Tracked attribute used as result works');
    ok(rv(Wrapper.new(value => 43)) == 43, 'Follow-up call does not fixate attribute read');
    ok($count == 1, 'Dispatch callback only invoked once');
    ok(rv(Subclass.new(value => 44)) == 44, 'On a subclass it also works');
    ok($count == 2, 'However, on a subclass implied guards are not met');
}

{
    my $target := -> $arg { nqp::dispatch('boot-resume', 'res-arg')  }
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'basic-resumable',
        # Dispatch
        -> $capture {
            nqp::dispatch('boot-syscall', 'dispatcher-set-resume-init-args', $capture);
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $capture, 0, $target);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        },
        # Resume
        -> $capture {
            nqp::die('In resume with arg ' ~ nqp::captureposarg_s($capture, 0));
        });
    my $message := '';
    try {
        nqp::dispatch('basic-resumable', 42);
        CATCH {
            $message := ~$_;
        }
    }
    ok($message ~~ /'In resume with arg'/, 'With boot-resume we make it into resume callback');
    ok($message ~~ /'res-arg'/, 'Resume callback gets expected argument');
}

{
    my $target-a := -> { nqp::dispatch('boot-resume') }
    my $target-b := -> { 'reached'  }
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'resumable-really-calls',
        # Dispatch
        -> $capture {
            nqp::dispatch('boot-syscall', 'dispatcher-set-resume-init-args', $capture);
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $capture, 0, $target-a);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        },
        # Resume
        -> $capture {
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $capture, 0, $target-b);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        });
    ok(nqp::dispatch('resumable-really-calls') eq 'reached',
        'resume callback can successfully provide code to run');
}

{
    my $target-a := -> $arg { 'x' ~ nqp::dispatch('boot-resume')  }
    my $target-b := -> $arg { 'y' ~ $arg }
    my int $disp-count;
    my int $res-count;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'resumable-using-init-args',
        # Dispatch
        -> $capture {
            $disp-count++;
            nqp::dispatch('boot-syscall', 'dispatcher-set-resume-init-args', $capture);
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $capture, 0, $target-a);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        },
        # Resume
        -> $capture {
            $res-count++;
            my $args := nqp::dispatch('boot-syscall', 'dispatcher-get-resume-init-args');
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $args, 0, $target-b);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        });
    sub test-call(str $arg) { nqp::dispatch('resumable-using-init-args', $arg) }

    ok(test-call('z') eq 'xyz', 'Resumption could access init args');
    ok($disp-count == 1, 'In dispatch function once');
    ok($res-count == 1, 'In resume function once');

    ok(test-call('Z') eq 'xyZ', 'Second call works and did not fixate init arg');
    ok($disp-count == 1, 'Still only in dispatch function once');
    ok($res-count == 1, 'Still only in resume function once');
}

{
    my $target-a := -> $arg { 'x' ~ ($arg ?? nqp::dispatch('boot-resume') !! '') }
    my $target-b := -> $arg { 'y' ~ $arg }
    my int $disp-count;
    my int $res-count;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'resumable-conditionally-resumed',
        # Dispatch
        -> $capture {
            $disp-count++;
            nqp::dispatch('boot-syscall', 'dispatcher-set-resume-init-args', $capture);
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $capture, 0, $target-a);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        },
        # Resume
        -> $capture {
            $res-count++;
            my $args := nqp::dispatch('boot-syscall', 'dispatcher-get-resume-init-args');
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $args, 0, $target-b);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        });
    sub test-call(str $arg) { nqp::dispatch('resumable-conditionally-resumed', $arg) }

    ok(test-call('') eq 'x', 'Code that conditionally resumes OK on first execution');
    ok($disp-count == 1, 'In dispatch function once');
    ok($res-count == 0, 'Not in resume function yet');

    ok(test-call('w') eq 'xyw', 'First resume taking place in second dispatch works');
    ok($disp-count == 1, 'Still only in dispatch function once');
    ok($res-count == 1, 'Now also in resume function once');

    ok(test-call('v') eq 'xyv', 'Second resume taking place in third dispatch works');
    ok($disp-count == 1, 'Still only in dispatch function once');
    ok($res-count == 1, 'Still only in resume function once');
}

{
    my $target-a := -> $arg { 'a' ~ nqp::dispatch('boot-resume')  }
    my $target-b1 := -> $arg { 'b1' }
    my $target-b2 := -> $arg { 'b2' }
    my class B1 {}
    my class B2 {}
    my int $disp-count;
    my int $res-count;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'resume-guarding-init-state',
        # Dispatch
        -> $capture {
            $disp-count++;
            nqp::dispatch('boot-syscall', 'dispatcher-set-resume-init-args', $capture);
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $capture, 0, $target-a);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        },
        # Resume
        -> $capture {
            # We insert a guard on the type and use it to choose where we will
            # dispatch to, to test guarding on resume init args.
            $res-count++;
            my $args := nqp::dispatch('boot-syscall', 'dispatcher-get-resume-init-args');
            my $arg := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $args, 0);
            nqp::dispatch('boot-syscall', 'dispatcher-guard-type', $arg);
            my $arg-val := nqp::captureposarg($args, 0);
            my $target := nqp::istype($arg-val, B1) ?? $target-b1 !! $target-b2;
            my $capture-derived := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $args, 0, $target);
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $capture-derived);
        });
    sub test-call($arg) { nqp::dispatch('resume-guarding-init-state', $arg) }

    ok(test-call(B1) eq 'ab1', 'Resumption that guards on type works');
    ok($disp-count == 1, 'In dispatch function once');
    ok($res-count == 1, 'In resume function once');

    ok(test-call(B1) eq 'ab1', 'Second call with same type also works');
    ok($disp-count == 1, 'Still only in dispatch function once');
    ok($res-count == 1, 'Still only in resume function once');

    ok(test-call(B2) eq 'ab2', 'Call with different type works');
    ok($disp-count == 1, 'Still only in dispatch function once as it is not type dependent');
    ok($res-count == 2, 'Was in resume function a second time due to type guard miss');

    ok(test-call(B2) eq 'ab2', 'Second call with different type works');
    ok($disp-count == 1, 'Still only in dispatch function once as it is not type dependent');
    ok($res-count == 2, 'Still only Was in resume function twice');

    ok(test-call(B1) eq 'ab1', 'Call using first type again still works');
    ok($disp-count == 1, 'Still only in dispatch function once');
    ok($res-count == 2, 'Still only in resume function twice');
}

# Used for building tests that emulate Raku method deferral, but rather
# simplified
class DeferralChain {
    has $!method;
    has $!next;
    method new($method, $next) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, DeferralChain, '$!method', $method);
        nqp::bindattr($obj, DeferralChain, '$!next', $next);
        $obj
    }
    method method() { $!method }
    method next() { $!next }
};
class Exhausted {};

{
    my class C1 { method m() { 'c1' } }
    my class C2 is C1 { method m() { 'c2' ~ nqp::dispatch('boot-resume') } }
    my class C3 is C2 { method m() { 'c3' ~ nqp::dispatch('boot-resume') } }
    my class C4 is C3 { method m() { 'c4' ~ nqp::dispatch('boot-resume') } }

    my int $disp-count;
    my int $res-count;
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'method-deferral',
        # Dispatch
        -> $capture {
            $disp-count++;
            # We'll resume on the original dispatch arguments.
            nqp::dispatch('boot-syscall', 'dispatcher-set-resume-init-args', $capture);

            # Guard on the method name and invocant type.
            my $name := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 0);
            nqp::dispatch('boot-syscall', 'dispatcher-guard-literal', $name);
            my $invocant := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $capture, 1);
            nqp::dispatch('boot-syscall', 'dispatcher-guard-type', $invocant);

            # Resolve the method.
            my str $name-val := nqp::captureposarg_s($capture, 0);
            my $invocant-val := nqp::captureposarg($capture, 1);
            my $meth := $invocant-val.HOW.find_method($invocant-val, $name-val);
            unless nqp::isconcrete($meth) {
                nqp::die("No such method '$meth'");
            }

            # Drop the name, insert the method, delegate.
            my $without-name := nqp::dispatch('boot-syscall',
                    'dispatcher-drop-arg', $capture, 0);
            my $with-method := nqp::dispatch('boot-syscall',
                    'dispatcher-insert-arg-literal-obj', $without-name, 0,
                    nqp::getattr($meth, NQPRoutine, '$!do'));
            nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                    'boot-code-constant', $with-method);
        },
        # Resume
        -> $capture {
            $res-count++;

            # Check if we have an existing dispatch state.
            my $state := nqp::dispatch('boot-syscall', 'dispatcher-get-resume-state');
            if nqp::isnull($state) {
                # No state, so just starting the resumption. Guard on the
                # invocant type and name.
                my $init := nqp::dispatch('boot-syscall', 'dispatcher-get-resume-init-args');
                my $name := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $init, 0);
                nqp::dispatch('boot-syscall', 'dispatcher-guard-literal', $name);
                my $invocant := nqp::dispatch('boot-syscall', 'dispatcher-track-arg', $init, 1);
                nqp::dispatch('boot-syscall', 'dispatcher-guard-type', $invocant);

                # Find all methods.
                my str $name-val := nqp::captureposarg_s($init, 0);
                my $invocant-val := nqp::captureposarg($init, 1);
                my @methods;
                for $invocant-val.HOW.mro($invocant-val) {
                    my $meth := $_.HOW.method_table($_){$name-val};
                    @methods.push($meth) if nqp::isconcrete($meth);
                }
                @methods.shift; # Discard the first one, which we initially called
                my $next-method := @methods.shift; # The immediate next one

                # Build chain of further methods and set it as the state.
                my $chain := Exhausted;
                while @methods {
                    $chain := DeferralChain.new(@methods.pop, $chain);
                }
                nqp::dispatch('boot-syscall', 'dispatcher-set-resume-state-literal', $chain);

                # Invoke the immediate next method.
                my $without-name := nqp::dispatch('boot-syscall',
                        'dispatcher-drop-arg', $init, 0);
                my $with-method := nqp::dispatch('boot-syscall',
                        'dispatcher-insert-arg-literal-obj', $without-name, 0,
                        nqp::getattr($next-method, NQPRoutine, '$!do'));
                nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                        'boot-code-constant', $with-method);
            }
            elsif nqp::istype($state, Exhausted) {
                nqp::die('Nowhere to defer to');
            }
            else {
                # Already working through a chain of things to dispatch on.
                # Obtain the tracking object for the dispatch state, and
                # guard against the method attribute.
                my $track-state := nqp::dispatch('boot-syscall', 'dispatcher-track-resume-state');
                my $track-method := nqp::dispatch('boot-syscall', 'dispatcher-track-attr',
                    $track-state, DeferralChain, '$!method');
                nqp::dispatch('boot-syscall', 'dispatcher-guard-literal', $track-method);

                # Update dispatch state to point to next method.
                my $track-next := nqp::dispatch('boot-syscall', 'dispatcher-track-attr',
                    $track-state, DeferralChain, '$!next');
                nqp::dispatch('boot-syscall', 'dispatcher-set-resume-state', $track-next);

                # Dispatch to the method at the head of the chain.
                my $init := nqp::dispatch('boot-syscall', 'dispatcher-get-resume-init-args');
                my $without-name := nqp::dispatch('boot-syscall',
                        'dispatcher-drop-arg', $init, 0);
                my $with-method := nqp::dispatch('boot-syscall',
                        'dispatcher-insert-arg-literal-obj', $without-name, 0,
                        nqp::getattr($state.method, NQPRoutine, '$!do'));
                nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                        'boot-code-constant', $with-method);
            }
        });
    sub test-call($obj) {
        nqp::dispatch('method-deferral', 'm', $obj)
    }

    ok(test-call(C1) eq 'c1', 'Non-resuming method deferral dispatch works');
    ok($disp-count == 1, 'Was in the dispatch callback once');
    ok($res-count == 0, 'Was never in the resume callback');

    ok(test-call(C2) eq 'c2c1', 'Single level of deferral works');
    ok($disp-count == 2, 'Was in the dispatch callback a second time');
    ok($res-count == 1, 'Was in the resume callback once');

    ok(test-call(C2) eq 'c2c1', 'Single level of deferral works with recorded program');
    ok($disp-count == 2, 'Was not in the dispatch callback again');
    ok($res-count == 1, 'Was not in the resume callback again');

    ok(test-call(C3) eq 'c3c2c1', 'Two levels of deferral works');
    ok($disp-count == 3, 'Was in the dispatch callback a third time');
    ok($res-count == 3, 'Was in the resume callback two more times as resumed twice');

    ok(test-call(C3) eq 'c3c2c1', 'Two levels of deferral works with recorded program');
    ok($disp-count == 3, 'Was not in the dispatch callback again');
    ok($res-count == 3, 'Was not in the resume callback again');

    ok(test-call(C4) eq 'c4c3c2c1', 'Three levels of deferral works');
    ok($disp-count == 4, 'Was in the dispatch callback a fourth time');
    ok($res-count == 5, 'Was in the resume callback twice more (by forth level, identical state)');

    ok(test-call(C4) eq 'c4c3c2c1', 'Three levels of deferral works with recorded program');
    ok($disp-count == 4, 'Was not in the dispatch callback again');
    ok($res-count == 5, 'Was not in the resume callback again');
}
