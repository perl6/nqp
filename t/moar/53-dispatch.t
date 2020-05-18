# Tests for the MoarVM dispatch mechanism

plan(4);

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
