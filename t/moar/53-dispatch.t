# Tests for the MoarVM dispatch mechanism

plan(57);

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
    ok(nqp::dispatch('call-on-target', 49) == 50,
        'dispatcher-insert-arg-literal-obj works at start of capture');
}

{
    my $target := -> $x, $y { $x ~ $y }
    nqp::dispatch('boot-syscall', 'dispatcher-register', 'insert-world', -> $capture {
        my $capture-derived := nqp::dispatch('boot-syscall',
                'dispatcher-insert-arg-literal-str', $capture, 2, 'world');
        nqp::dispatch('boot-syscall', 'dispatcher-delegate',
                'boot-code-constant', $capture-derived);
    });
    ok(nqp::dispatch('insert-world', $target, 'hello ') eq 'hello world',
        'dispatcher-insert-arg-literal-str works at end of capture');
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
    ok(nqp::dispatch('dupe-arg', $adder, 3) == 9, 'Can duplicate an argument');
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
