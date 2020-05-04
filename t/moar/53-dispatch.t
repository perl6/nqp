# Tests for the MoarVM dispatch mechanism

plan(2);

{
    sub value($x) {
        nqp::dispatch('boot-value', $x)
    }

    ok(value(1) == 1, 'boot-value passes through value');
    ok(value(2) == 2, 'boot-value does not fixate value');
}
