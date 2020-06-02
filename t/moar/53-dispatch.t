# Tests for the MoarVM dispatch mechanism

plan(32);

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
    class C1 { }
    class C2 { }
    class C3 { }
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
