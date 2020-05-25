# Tests for the MoarVM dispatch mechanism

plan(17);

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
