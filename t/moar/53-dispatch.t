# Tests for the MoarVM dispatch mechanism

plan(6);

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
