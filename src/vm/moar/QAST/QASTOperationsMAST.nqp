my int $MVM_operand_literal     := 0;
my int $MVM_operand_read_reg    := 1;
my int $MVM_operand_write_reg   := 2;
my int $MVM_operand_read_lex    := 3;
my int $MVM_operand_write_lex   := 4;
my int $MVM_operand_rw_mask     := 7;

my int $MVM_operand_int8        := ($MVM_reg_int8 * 8);
my int $MVM_operand_int16       := ($MVM_reg_int16 * 8);
my int $MVM_operand_int32       := ($MVM_reg_int32 * 8);
my int $MVM_operand_int64       := ($MVM_reg_int64 * 8);
my int $MVM_operand_num32       := ($MVM_reg_num32 * 8);
my int $MVM_operand_num64       := ($MVM_reg_num64 * 8);
my int $MVM_operand_str         := ($MVM_reg_str * 8);
my int $MVM_operand_obj         := ($MVM_reg_obj * 8);
my int $MVM_operand_ins         := (9 * 8);
my int $MVM_operand_type_var    := (10 * 8);
my int $MVM_operand_lex_outer   := (11 * 8);
my int $MVM_operand_coderef     := (12 * 8);
my int $MVM_operand_callsite    := (13 * 8);
my int $MVM_operand_type_mask   := (31 * 8);
my int $MVM_operand_uint8       := ($MVM_reg_uint8 * 8);
my int $MVM_operand_uint16      := ($MVM_reg_uint16 * 8);
my int $MVM_operand_uint32      := ($MVM_reg_uint32 * 8);
my int $MVM_operand_uint64      := ($MVM_reg_uint64 * 8);

my %core_op_generators    := MAST::Ops.WHO<%generators>;
my &op_decont := %core_op_generators<decont>;
my &op_goto   := %core_op_generators<goto>;
my &op_null   := %core_op_generators<null>;
my &op_set    := %core_op_generators<set>;

my uint $op_code_prepargs     := %MAST::Ops::codes<prepargs>;
my uint $op_code_argconst_s   := %MAST::Ops::codes<argconst_s>;
my uint $op_code_invoke_v     := %MAST::Ops::codes<invoke_v>;
my uint $op_code_invoke_i     := %MAST::Ops::codes<invoke_i>;
my uint $op_code_invoke_n     := %MAST::Ops::codes<invoke_n>;
my uint $op_code_invoke_s     := %MAST::Ops::codes<invoke_s>;
my uint $op_code_invoke_o     := %MAST::Ops::codes<invoke_o>;
my uint $op_code_speshresolve := %MAST::Ops::codes<speshresolve>;

# This is used as a return value from all of the various compilation routines.
# It groups together a set of instructions along with a result register and a
# result kind.  It also tracks the source filename and line number.
class MAST::InstructionList {
    has $!result_reg;
    has int $!result_kind;

    method new($result_reg, int $result_kind) {
        my $obj := nqp::create(self);
        nqp::bindattr($obj, MAST::InstructionList, '$!result_reg', $result_reg);
        nqp::bindattr_i($obj, MAST::InstructionList, '$!result_kind', $result_kind);
        $obj
    }

    method result_reg()   { $!result_reg }
    method result_kind()  { $!result_kind }

    method append(MAST::InstructionList $other) {
        $!result_reg := $other.result_reg;
        $!result_kind := nqp::unbox_i($other.result_kind);
    }
}

# Marker object for void.
class MAST::VOID { }

class QAST::MASTOperations {

    # Maps operations to code that will handle them. Hash of code.
    my %core_ops;

    # Maps HLL-specific operations to code that will handle them.
    # Hash of hash of code.
    my %hll_ops;

    # Mapping of how to box/unbox by HLL.
    my %hll_box;
    my %hll_unbox;

    # What we know about inlinability.
    my %core_inlinability;
    my %hll_inlinability;

    # What we know about op native results types.
    my %core_result_type;
    my %hll_result_type;

    # Compiles an operation to MAST.
    method compile_op($qastcomp, $hll, $op) {
        my str $name := $op.op;
        my $mapper;
        if $hll {
            my %ops := %hll_ops{$hll};
            $mapper := %ops{$name} if nqp::isconcrete(%ops) && nqp::elems(%ops);
        }
        $mapper := %core_ops{$name} unless $mapper;
        $mapper
            ?? $mapper($qastcomp, $op)
            !! nqp::die("No registered operation handler for '$name'");
    }

    my @kind_names := ['VOID','int8','int16','int32','int','num32','num','str','obj'];
    my @kind_types := [0,1,1,1,1,2,2,3,4];

    my @core_operands_offsets := MAST::Ops.WHO<@offsets>;
    my @core_operands_counts  := MAST::Ops.WHO<@counts>;
    my @core_operands_values  := MAST::Ops.WHO<@values>;
    my %core_op_codes         := MAST::Ops.WHO<%codes>;
    method compile_mastop($qastcomp, str $op, @args, @deconts, :$returnarg = -1, :$want) {
        # Resolve as either core op or ext op.
        my int $num_operands;
        my int $operands_offset;
        my int $is_extop;
        my @operands_values;
        if nqp::existskey(%core_op_codes, $op) {
            my int $op_num   := %core_op_codes{$op};
            $num_operands    := nqp::atpos_i(@core_operands_counts, $op_num);
            $operands_offset := nqp::atpos_i(@core_operands_offsets, $op_num);
            @operands_values := @core_operands_values;
            $is_extop := 0;
        }
        elsif MAST::ExtOpRegistry.extop_known($op) {
            @operands_values := MAST::ExtOpRegistry.extop_signature($op);
            $num_operands    := nqp::elems(@operands_values);
            $operands_offset := 0;
            $is_extop := 1;
        }
        else {
            nqp::die("MoarVM op '$op' is unknown as a core or extension op");
        }

        my int $num_args := +@args;
        my int $operand_num := 0;
        my int $result_kind := $MVM_reg_void;
        my $result_reg := MAST::VOID;
        my int $needs_write := 0;
        my int $type_var_kind := 0;
        my $regalloc := $*REGALLOC;

        my @arg_regs;
        my @release_regs;
        my @release_kinds;

        # if the op has operands, and the first operand is a write register,
        # and the number of args provided is one less than the number of operands needed,
        # mark that we need to generate a result register at the end, and
        # advance to the second operand.
        if ($num_operands
                && (nqp::atpos_i(@operands_values, $operands_offset) +& $MVM_operand_rw_mask) == $MVM_operand_write_reg
                    # allow the QASTree to define its own write register
                && $num_args == $num_operands - 1) {
            $needs_write := 1;
            $operand_num++;
        }

        if ($num_args != $num_operands - $operand_num) {
            nqp::die("Arg count $num_args doesn't equal required operand count "~($num_operands - $operand_num)~" for op '$op'");
        }

        if ($op eq 'return') {
            $*BLOCK.return_kind($MVM_reg_void);
        }

        my int $arg_num := 0;
        # Compile provided args.
        for @args {
            my int $operand := nqp::atpos_i(@operands_values, $operands_offset + $operand_num++);
            my int $operand_kind := ($operand +& $MVM_operand_type_mask);
            my int $constant_operand := !($operand +& $MVM_operand_rw_mask);
            my $want-decont := @deconts[$arg_num];
            my $arg := $operand_kind == $MVM_operand_type_var
                ?? $qastcomp.as_mast($_, :$want-decont)
                !! $qastcomp.as_mast($_, :want(nqp::bitshiftr_i($operand_kind, 3)), :$want-decont);
            my int $arg_kind := nqp::unbox_i($arg.result_kind);

            if $arg_num == 0 && nqp::eqat($op, 'return_', 0) {
                $*BLOCK.return_kind(nqp::unbox_i($arg.result_kind));
            }

            # args cannot be void
            if $arg_kind == $MVM_reg_void {
                nqp::die("Cannot use a void register as an argument to op '$op'");
            }

            if ($operand_kind == $MVM_operand_type_var) {
                # handle ops that have type-variables as operands
                if ($type_var_kind) {
                    # if we've already seen a type-var
                    if ($arg_kind != $type_var_kind) {
                        # the arg types must match
                        nqp::die("variable-type op '$op' requires same-typed args");
                    }
                }
                else {
                    # set this variable-type op's typecode
                    $type_var_kind := $arg_kind;
                }
            } # allow nums and ints to be bigger than their destination width
            elsif (@kind_types[$arg_kind] != @kind_types[nqp::bitshiftr_i($operand_kind, 3)]) {
                $qastcomp.coerce($arg, nqp::bitshiftr_i($operand_kind, 3));
                $arg_kind := nqp::bitshiftr_i($operand_kind, 3);
                # the arg typecode left shifted 3 must match the operand typecode
            #    nqp::die("arg type {@kind_names[$arg_kind]} does not match operand type {@kind_names[nqp::bitshiftr_i($operand_kind, 3)]} to op '$op'");
            }

            # if this is the write register, get the result reg and type from it
            if ($operand +& $MVM_operand_rw_mask) == $MVM_operand_write_reg
                || ($operand +& $MVM_operand_rw_mask) == $MVM_operand_write_lex
                || $returnarg != -1 && $returnarg == $arg_num {
                $result_reg := $arg.result_reg;
                $result_kind := $arg_kind;
            }
            # otherwise it's a read register, so it can be released if it's an
            # intermediate value
            else {
                # if it's not a write register, queue it to be released it to the allocator
                nqp::push(@release_regs, $arg.result_reg);
                nqp::push(@release_kinds, $arg_kind);
            }

            # put the arg expression's generation code in the instruction list
            if @deconts[$arg_num] &&
                    (!$_.has_compile_time_value || nqp::iscont($_.compile_time_value)) {
                my $dc_reg := $regalloc.fresh_register($MVM_reg_obj);
                MAST::Op.new( :op('decont'), $dc_reg, $arg.result_reg );
                nqp::push(@arg_regs, $dc_reg);
                nqp::push(@release_regs, $dc_reg);
                nqp::push(@release_kinds, $MVM_reg_obj);
            }
            else {
                nqp::push(@arg_regs, $constant_operand
                    ?? $qastcomp.as_mast_constant($_)
                    !! $arg.result_reg);
            }

            $arg_num++;
        }

        # release the registers to the allocator. See comment there.
        my int $release_i := 0;
        $regalloc.release_register($_, @release_kinds[$release_i++]) for @release_regs;

        # unshift in a generated write register arg if it needs one
        if ($needs_write) {
            # do this after the args to possibly reuse a register,
            # and so we know the type of result register for ops with type_var operands.

            $result_kind := (nqp::atpos_i(@operands_values, $operands_offset) +& $MVM_operand_type_mask) / 8;

            # fixup the variable typecode if there is one
            if ($type_var_kind && $result_kind == $MVM_operand_type_var / 8) {
                $result_kind := $type_var_kind;
            }

            $result_reg := $regalloc.fresh_register($result_kind);

            nqp::unshift(@arg_regs, $result_reg);
        }

        # Add operation node.
        if $is_extop {
            MAST::ExtOp.new_with_operand_array( :op($op), :cu($qastcomp.mast_compunit), @arg_regs )
        }
        else {
            %core_op_generators{$op}(|@arg_regs);
        }

        # Build instruction list.
        nqp::defined($want)
            ?? $qastcomp.coerce(MAST::InstructionList.new($result_reg, $result_kind), $want)
            !! MAST::InstructionList.new($result_reg, $result_kind);
    }

    # Adds a core op handler.
    method add_core_op(str $op, $handler, :$inlinable = 1) {
        %core_ops{$op} := $handler;
        self.set_core_op_inlinability($op, $inlinable);
    }

    # Adds a HLL op handler.
    method add_hll_op(str $hll, str $op, $handler, :$inlinable = 1) {
        %hll_ops{$hll} := {} unless %hll_ops{$hll};
        %hll_ops{$hll}{$op} := $handler;
        self.set_hll_op_inlinability($hll, $op, $inlinable);
    }

    # Sets op inlinability at a core level.
    method set_core_op_inlinability(str $op, $inlinable) {
        %core_inlinability{$op} := $inlinable;
    }

    # Sets op inlinability at a HLL level. (Can override at HLL level whether
    # or not the HLL overrides the op itself.)
    method set_hll_op_inlinability(str $hll, str $op, $inlinable) {
        %hll_inlinability{$hll} := {} unless nqp::existskey(%hll_inlinability, $hll);
        %hll_inlinability{$hll}{$op} := $inlinable;
    }

    # Checks if an op is considered inlinable.
    method is_inlinable(str $hll, str $op) {
        if nqp::existskey(%hll_inlinability, $hll) {
            if nqp::existskey(%hll_inlinability{$hll}, $op) {
                return %hll_inlinability{$hll}{$op};
            }
        }
        return %core_inlinability{$op} // 0;
    }

    # Adds a core op that maps to a Moar op.
    method add_core_moarop_mapping(str $op, str $moarop, $ret = -1, :$decont, :$inlinable = 1) {
        %core_ops{$op} := self.moarop_mapper($moarop, $ret, $decont);
        self.set_core_op_inlinability($op, $inlinable);
        self.set_core_op_result_type($op, moarop_return_type($moarop));
    }

    # Adds a HLL op that maps to a Moar op.
    method add_hll_moarop_mapping(str $hll, str $op, str $moarop, $ret = -1, :$decont, :$inlinable = 1) {
        %hll_ops{$hll} := {} unless %hll_ops{$hll};
        %hll_ops{$hll}{$op} := self.moarop_mapper($moarop, $ret, $decont);
        self.set_hll_op_inlinability($hll, $op, $inlinable);
        self.set_hll_op_result_type($hll, $op, moarop_return_type($moarop));
    }

    method check_ret_val(str $moarop, int $ret) {
        my int $num_operands;
        my int $operands_offset;
        my @operands_values;
        if nqp::existskey(%core_op_codes, $moarop) {
            my int $op_num   := %core_op_codes{$moarop};
            $num_operands    := nqp::atpos_i(@core_operands_counts, $op_num);
            $operands_offset := nqp::atpos_i(@core_operands_offsets, $op_num);
            @operands_values := @core_operands_values;
        }
        elsif MAST::ExtOpRegistry.extop_known($moarop) {
            @operands_values := MAST::ExtOpRegistry.extop_signature($moarop);
            $num_operands    := nqp::elems(@operands_values);
            $operands_offset := 0;
        }
        else {
            nqp::die("MoarVM op '$moarop' is unknown as a core or extension op");
        }
        nqp::die("moarop $moarop return arg index $ret out of range -1.." ~ $num_operands - 1)
            if $ret < -1 || $ret >= $num_operands;
        nqp::die("moarop $moarop is not void")
            if $num_operands && (nqp::atpos_i(@operands_values, $operands_offset) +& $MVM_operand_rw_mask) ==
                $MVM_operand_write_reg;
    }

    # Returns a mapper closure for turning an operation into a Moar op.
    # $ret is the 0-based index of which arg to use as the result when
    # the moarop is void.
    method moarop_mapper(str $moarop, int $ret, $decont_in) {
        # do a little checking of input values

        my $self := self;

        if $ret != -1 {
            self.check_ret_val($moarop, $ret);
        }

        my @deconts;
        if nqp::islist($decont_in) {
            for $decont_in { @deconts[$_] := 1; }
        }
        elsif nqp::defined($decont_in) {
            @deconts[$decont_in] := 1;
        }

        -> $qastcomp, $op {
            $self.compile_mastop($qastcomp, $moarop, $op.list, @deconts, :returnarg($ret))
        }
    }

    # Gets the return type of a MoarVM op, if any.
    sub moarop_return_type(str $moarop) {
        if nqp::existskey(%core_op_codes, $moarop) {
            my int $op_num       := %core_op_codes{$moarop};
            my int $num_operands := nqp::atpos_i(@core_operands_counts, $op_num);
            if $num_operands {
                my int $operands_offset := nqp::atpos_i(@core_operands_offsets, $op_num);
                my int $ret_sig         := nqp::atpos_i(@core_operands_values, $operands_offset);
                if ($ret_sig +& $MVM_operand_rw_mask) == $MVM_operand_write_reg {
                    return nqp::bitshiftr_i($ret_sig, 3);
                }
            }
        }
        elsif MAST::ExtOpRegistry.extop_known($moarop) {
            my @operands_values := MAST::ExtOpRegistry.extop_signature($moarop);
            if @operands_values {
                my int $ret_sig := nqp::atpos_i(@operands_values, 0);
                if ($ret_sig +& $MVM_operand_rw_mask) == $MVM_operand_write_reg {
                    return nqp::bitshiftr_i($ret_sig, 3);
                }
            }
        }
        else {
            nqp::die("MoarVM op '$moarop' is unknown as a core or extension op");
        }
        0
    }

    # Sets op native result type at a core level.
    method set_core_op_result_type(str $op, int $type) {
        if $type == $MVM_reg_int64 {
            %core_result_type{$op} := int;
        }
        elsif $type == $MVM_reg_num64 {
            %core_result_type{$op} := num;
        }
        elsif $type == $MVM_reg_str {
            %core_result_type{$op} := str;
        }
    }

    # Sets op inlinability at a HLL level. (Can override at HLL level whether
    # or not the HLL overrides the op itself.)
    method set_hll_op_result_type(str $hll, str $op, int $type) {
        %hll_result_type{$hll} := {} unless nqp::existskey(%hll_result_type, $hll);
        if $type == $MVM_reg_int64 {
            %hll_result_type{$hll}{$op} := int;
        }
        elsif $type == $MVM_reg_num64 {
            %hll_result_type{$hll}{$op} := num;
        }
        elsif $type == $MVM_reg_str {
            %hll_result_type{$hll}{$op} := str;
        }
    }

    # Sets returns on an op node if we it has a native result type.
    method attach_result_type(str $hll, $node) {
        my $op := $node.op;
        if nqp::existskey(%hll_result_type, $hll) {
            if nqp::existskey(%hll_result_type{$hll}, $op) {
                $node.returns(%hll_result_type{$hll}{$op});
                return 1;
            }
        }
        if nqp::existskey(%core_result_type, $op) {
            $node.returns(%core_result_type{$op});
        }
    }

    # Adds a HLL box handler.
    method add_hll_box(str $hll, int $type, $handler) {
        unless $type == $MVM_reg_int64 || $type == $MVM_reg_num64 || $type == $MVM_reg_str ||
                $type == $MVM_reg_uint64 || $type == $MVM_reg_void {
            nqp::die("Unknown box type '$type'");
        }
        %hll_box{$hll} := {} unless nqp::existskey(%hll_box, $hll);
        %hll_box{$hll}{$type} := $handler;
    }

    # Adds a HLL unbox handler.
    method add_hll_unbox(str $hll, int $type, $handler) {
        unless $type == $MVM_reg_int64 || $type == $MVM_reg_num64 ||
                $type == $MVM_reg_str || $type == $MVM_reg_uint64 {
            nqp::die("Unknown unbox type '$type'");
        }
        %hll_unbox{$hll} := {} unless nqp::existskey(%hll_unbox, $hll);
        %hll_unbox{$hll}{$type} := $handler;
    }

    # Generates instructions to box the result in reg.
    method box($qastcomp, str $hll, $type, $reg) {
        (%hll_box{$hll}{$type} // %hll_box{''}{$type})($qastcomp, $reg)
    }

    # Generates instructions to unbox the result in reg.
    method unbox($qastcomp, str $hll, $type, $reg) {
        (%hll_unbox{$hll}{$type} // %hll_unbox{''}{$type})($qastcomp, $reg)
    }
}

# Set of sequential statements
QAST::MASTOperations.add_core_op('stmts', -> $qastcomp, $op {
    $qastcomp.as_mast(QAST::Stmts.new( |@($op) ))
});

my sub pre-size-array($qastcomp, $instructionlist, $array_reg, $size) {
    if $size != 1 {
        my $int_reg := $*REGALLOC.fresh_i();
        my int $size_i := +$size;
        %core_op_generators{'const_i64'}($int_reg, $size_i);
        %core_op_generators{'setelemspos'}($array_reg, $int_reg);
        # reset the number of elements to 0 so that we don't push to the end
        # since our lists don't shrink by themselves (or by setting elems), we'll
        # end up with enough storage to hold all elements exactly
        %core_op_generators{'const_i64'}($int_reg, 0);
        %core_op_generators{'setelemspos'}($array_reg, $int_reg);
        $*REGALLOC.release_register($int_reg, $MVM_reg_int64);
    }
}

# Data structures
QAST::MASTOperations.add_core_op('list', -> $qastcomp, $op {
    # Just desugar to create the empty list.
    my $regalloc := $*REGALLOC;
    my $arr := $qastcomp.as_mast(QAST::Op.new(
        :op('create'),
        QAST::Op.new( :op('hlllist') )
    ));
    if nqp::elems($op.list) {
        my $arr_reg := $arr.result_reg;
        pre-size-array($qastcomp, $arr, $arr_reg, nqp::elems($op.list));
        # Push things to the list.
        for $op.list {
            my $item := $qastcomp.as_mast($_, :want($MVM_reg_obj));
            my $item_reg := $item.result_reg;
            $arr.append($item);
            %core_op_generators{'push_o'}($arr_reg, $item_reg);
            $regalloc.release_register($item_reg, $MVM_reg_obj);
        }
        my $ensure_return_register := MAST::InstructionList.new($arr_reg, $MVM_reg_obj);
        $arr.append($ensure_return_register);
    }
    $arr
});
QAST::MASTOperations.add_core_op('list_i', -> $qastcomp, $op {
    # Just desugar to create the empty list.
    my $regalloc := $*REGALLOC;
    my $arr := $qastcomp.as_mast(QAST::Op.new(
        :op('create'),
        QAST::Op.new( :op('bootintarray') )
    ));
    if nqp::elems($op.list) {
        my $arr_reg := $arr.result_reg;
        pre-size-array($qastcomp, $arr, $arr_reg, nqp::elems($op.list));
        # Push things to the list.
        for $op.list {
            my $item := $qastcomp.as_mast($_, :want($MVM_reg_int64));
            my $item_reg := $item.result_reg;
            $arr.append($item);
            %core_op_generators{'push_i'}($arr_reg, $item_reg);
            $regalloc.release_register($item_reg, $MVM_reg_int64);
        }
        my $ensure_return_register := MAST::InstructionList.new($arr_reg, $MVM_reg_obj);
        $arr.append($ensure_return_register);
    }
    $arr
});
QAST::MASTOperations.add_core_op('list_n', -> $qastcomp, $op {
    # Just desugar to create the empty list.
    my $regalloc := $*REGALLOC;
    my $arr := $qastcomp.as_mast(QAST::Op.new(
        :op('create'),
        QAST::Op.new( :op('bootnumarray') )
    ));
    if nqp::elems($op.list) {
        my $arr_reg := $arr.result_reg;
        pre-size-array($qastcomp, $arr, $arr_reg, nqp::elems($op.list));
        # Push things to the list.
        for $op.list {
            my $item := $qastcomp.as_mast($_, :want($MVM_reg_num64));
            my $item_reg := $item.result_reg;
            $arr.append($item);
            %core_op_generators{'push_n'}($arr_reg, $item_reg);
            $regalloc.release_register($item_reg, $MVM_reg_num64);
        }
        my $ensure_return_register := MAST::InstructionList.new($arr_reg, $MVM_reg_obj);
        $arr.append($ensure_return_register);
    }
    $arr
});
QAST::MASTOperations.add_core_op('list_s', -> $qastcomp, $op {
    # Just desugar to create the empty list.
    my $regalloc := $*REGALLOC;
    my $arr := $qastcomp.as_mast(QAST::Op.new(
        :op('create'),
        QAST::Op.new( :op('bootstrarray') )
    ));
    if nqp::elems($op.list) {
        my $arr_reg := $arr.result_reg;
        pre-size-array($qastcomp, $arr, $arr_reg, nqp::elems($op.list));
        # Push things to the list.
        for $op.list {
            my $item := $qastcomp.as_mast($_, :want($MVM_reg_str));
            my $item_reg := $item.result_reg;
            $arr.append($item);
            %core_op_generators{'push_s'}($arr_reg, $item_reg);
            $regalloc.release_register($item_reg, $MVM_reg_str);
        }
        my $ensure_return_register := MAST::InstructionList.new($arr_reg, $MVM_reg_obj);
        $arr.append($ensure_return_register);
    }
    $arr
});
QAST::MASTOperations.add_core_op('list_b', -> $qastcomp, $op {
    # Just desugar to create the empty list.
    my $regalloc := $*REGALLOC;
    my $arr := $qastcomp.as_mast(QAST::Op.new(
        :op('create'),
        QAST::Op.new( :op('bootarray') )
    ));
    if nqp::elems($op.list) {
        my $arr_reg := $arr.result_reg;
        pre-size-array($qastcomp, $arr, $arr_reg, nqp::elems($op.list));
        # Push things to the list.
        my $item_reg := $regalloc.fresh_register($MVM_reg_obj);
        for $op.list {
            nqp::die("The 'list_b' op needs a list of blocks, got " ~ $_.HOW.name($_))
                unless nqp::istype($_, QAST::Block);
            my $cuid  := $_.cuid();
            my $frame := $qastcomp.mast_frames{$cuid};
            %core_op_generators{'getcode'}($item_reg, $frame);
            %core_op_generators{'push_o'}($arr_reg, $item_reg);
        }
        $regalloc.release_register($item_reg, $MVM_reg_obj);
        my $ensure_return_register := MAST::InstructionList.new($arr_reg, $MVM_reg_obj);
        $arr.append($ensure_return_register);
    }
    $arr
});
QAST::MASTOperations.add_core_op('numify', -> $qastcomp, $op {
    $qastcomp.as_mast($op[0], :want($MVM_reg_num64))
});
QAST::MASTOperations.add_core_op('intify', -> $qastcomp, $op {
    $qastcomp.as_mast($op[0], :want($MVM_reg_int64))
});
QAST::MASTOperations.add_core_op('hash', -> $qastcomp, $op {
    # Just desugar to create the empty hash.
    my $regalloc := $*REGALLOC;
    my $hash := $qastcomp.as_mast(QAST::Op.new(
        :op('create'),
        QAST::Op.new( :op('hllhash') )
    ));
    if nqp::elems($op.list) {
        my $hash_reg := $hash.result_reg;
        for $op.list -> $key, $val {
            my $key_mast := $qastcomp.as_mast($key, :want($MVM_reg_str));
            my $val_mast := $qastcomp.as_mast($val, :want($MVM_reg_obj));
            my $key_reg := $key_mast.result_reg;
            my $val_reg := $val_mast.result_reg;
            $hash.append($key_mast);
            $hash.append($val_mast);
            %core_op_generators{'bindkey_o'}($hash_reg, $key_reg, $val_reg);
            $regalloc.release_register($key_reg, $MVM_reg_str);
            $regalloc.release_register($val_reg, $MVM_reg_obj);
        }
        my $ensure_return_register := MAST::InstructionList.new($hash_reg, $MVM_reg_obj);
        $hash.append($ensure_return_register);
    }
    $hash
});

# Chaining.
# TODO: Provide static-optimizations where possible for invocations involving metaops
my $chain_gen := sub ($qastcomp, $op) {
    # First, we build up the list of nodes in the chain
    my @clist;
    my $cqast := $op;

    # Check if callee sub in name, if not first child is callee, not arg
    my $arg_idx;
    my &get_arg_idx := -> $cq { $cq.name ?? 0 !! 1 };

    while nqp::istype($cqast, QAST::Op)
    && ($cqast.op eq 'chain' || $cqast.op eq 'chainstatic') {
        nqp::push(@clist, $cqast);
        $arg_idx := get_arg_idx($cqast);
        $cqast := $cqast[$arg_idx];
    }

    my $regalloc := $*REGALLOC;
    my $res_reg  := $regalloc.fresh_register($MVM_reg_obj);
    my $endlabel := MAST::Label.new();

    $cqast := nqp::pop(@clist);
    $arg_idx := get_arg_idx($cqast);

    my $aqast := $cqast[$arg_idx];
    my $acomp := $qastcomp.as_mast($aqast, :want($MVM_reg_obj));

    my $more := 1;
    while $more {
        my $bqast := $cqast[$arg_idx + 1];
        my $bcomp := $qastcomp.as_mast($bqast, :want($MVM_reg_obj));

        my $callee := $qastcomp.as_mast: :want($MVM_reg_obj),
            !$cqast.name
                ?? $cqast[0]
                !! $cqast.op eq 'chainstatic'
                    ?? QAST::VM.new:   :moarop<getlexstatic_o>,
                       QAST::SVal.new: :value($cqast.name)
                    !! QAST::Var.new:  :name( $cqast.name), :scope<lexical>;

        MAST::Call.new(
            :target($callee.result_reg),
            :flags([$Arg::obj, $Arg::obj]),
            :result($res_reg),
            $acomp.result_reg, $bcomp.result_reg
        );

        $regalloc.release_register($callee.result_reg, $MVM_reg_obj);
        $regalloc.release_register($acomp.result_reg, $MVM_reg_obj);

        if @clist {
            %core_op_generators{'unless_o'}($res_reg, $endlabel);
            $cqast := nqp::pop(@clist);
            $arg_idx := get_arg_idx($cqast);
            $acomp := $bcomp;
        }
        else {
            $more := 0;
        }
    }

    $*MAST_FRAME.add-label($endlabel);
    MAST::InstructionList.new($res_reg, $MVM_reg_obj)
}
QAST::MASTOperations.add_core_op: 'chain',       $chain_gen;
QAST::MASTOperations.add_core_op: 'chainstatic', $chain_gen;

# Conditionals.
sub needs_cond_passed($n) {
    nqp::istype($n, QAST::Block)
    && ($n.arity > 0 || $n.ann: 'count') # slurpies would have .arity 0
    && ($n.blocktype eq 'immediate' || $n.blocktype eq 'immediate_static')
}
for <if unless with without> -> $op_name {
    QAST::MASTOperations.add_core_op($op_name, -> $qastcomp, $op {
        # Check operand count.
        my $operands := nqp::elems($op.list);
        nqp::die("The '$op_name' op needs 2 or 3 operands, got $operands")
            if $operands < 2 || $operands > 3;

        my $regalloc := $*REGALLOC;

        # Compile each of the children, handling any that want the conditional
        # value to be passed.
        my $is_void := nqp::defined($*WANT) && $*WANT == $MVM_reg_void;
        my $wanted  := $is_void ?? $MVM_reg_void !! NQPMu;
        my @comp_ops;
        my $is_withy := $op_name eq 'with' || $op_name eq 'without';

        # Create labels.
        my $if_id    := $qastcomp.unique($op_name);
        my $end_lbl  := MAST::Label.new();
        my $else_lbl := MAST::Label.new();
        my $cond_temp_lbl := $is_withy || needs_cond_passed($op[1]) || needs_cond_passed($op[2])
            ?? $qastcomp.unique('__im_cond_')
            !! '';

        # Evaluate the condition first; store result if needed.
        if $cond_temp_lbl {
            if $is_withy {
                @comp_ops[0] := $qastcomp.as_mast(QAST::Op.new(
                    :op('bind'),
                    QAST::Var.new( :name($cond_temp_lbl), :scope('local'), :decl('var') ),
                    $op[0]), :want($MVM_reg_obj));
            } else {
                @comp_ops[0] := $qastcomp.as_mast(QAST::Op.new(
                    :op('bind'),
                    QAST::Var.new( :name($cond_temp_lbl), :scope('local'), :decl('var') ),
                    $op[0]));
            }
        }
        elsif nqp::istype($op[0], QAST::Var)
        && $op[0].scope eq 'lexicalref'
        && (!$*WANT || $operands == 3) {
            # lexical refs are expensive; try to coerce them to something cheap
            my $spec := nqp::objprimspec($op[0].returns);
            @comp_ops[0] := $qastcomp.as_mast(:want(
                $spec == 1 ?? $MVM_reg_int64 !!
                $spec == 2 ?? $MVM_reg_num64 !!
                $spec == 3 ?? $MVM_reg_str   !!
                              $MVM_reg_obj
            ), $op[0]);
        }
        else {
            @comp_ops[0] := $qastcomp.as_mast($op[0]);
        }

        $*MAST_FRAME.start_subbuffer;

        if needs_cond_passed($op[1]) {
            my $orig_type := $op[1].blocktype;
            $op[1].blocktype('declaration');
            @comp_ops[1] := $qastcomp.as_mast(QAST::Op.new(
                :op('call'),
                $op[1],
                QAST::Var.new( :name($cond_temp_lbl), :scope('local') )),
                :want($wanted));
            $op[1].blocktype($orig_type);
        }
        else {
            @comp_ops[1] := $qastcomp.as_mast($op[1], :want($wanted), :want-decont($*WANT-DECONT));
        }

        if (nqp::unbox_i(@comp_ops[0].result_kind) == $MVM_reg_void) {
            nqp::die("The '$op_name' op condition cannot be void, cannot use the results of '" ~ $op[0].op ~ "'");
        }

        my $then-subbuffer := $*MAST_FRAME.end_subbuffer;
        my $else-subbuffer;

        if needs_cond_passed($op[2]) {
            my $orig_type := $op[2].blocktype;
            $op[2].blocktype('declaration');
            $*MAST_FRAME.start_subbuffer;
            @comp_ops[2] := $qastcomp.as_mast(QAST::Op.new(
                :op('call'),
                $op[2],
                QAST::Var.new( :name($cond_temp_lbl), :scope('local') )),
                :want($wanted));
            $else-subbuffer := $*MAST_FRAME.end_subbuffer;
            $op[2].blocktype($orig_type);
        }
        elsif $op[2] {
            $*MAST_FRAME.start_subbuffer;
            @comp_ops[2] := $qastcomp.as_mast($op[2], :want($wanted), :want-decont($*WANT-DECONT));
            $else-subbuffer := $*MAST_FRAME.end_subbuffer;
        }


        my int $res_kind;
        my $res_reg;
        if $is_void {
            $res_reg := MAST::VOID;
            $res_kind := $MVM_reg_void;
        }
        else {
            $res_kind := $operands == 3
            ?? (
                @comp_ops[1].result_kind == @comp_ops[2].result_kind
                    && @comp_ops[1].result_kind != $MVM_reg_void
                ?? nqp::unbox_i(@comp_ops[1].result_kind)
                !! $MVM_reg_obj
            )
            !!
                (@comp_ops[0].result_kind == @comp_ops[1].result_kind
                    ?? nqp::unbox_i(@comp_ops[0].result_kind)
                    !! $MVM_reg_obj);
            $res_reg := $regalloc.fresh_register($res_kind);
        }

        if $operands == 2 && !$is_void {
            my $il := MAST::InstructionList.new(@comp_ops[0].result_reg, nqp::unbox_i(@comp_ops[0].result_kind));
            $qastcomp.coerce($il, $res_kind);
            op_set($res_reg, $il.result_reg);
        }

        # Emit the jump.
        if nqp::unbox_i(@comp_ops[0].result_kind) == $MVM_reg_obj {
            my $decont_reg := $regalloc.fresh_register($MVM_reg_obj);
            op_decont($decont_reg, @comp_ops[0].result_reg);
            if $is_withy {
                my $method_reg := $regalloc.fresh_register($MVM_reg_obj);
                %core_op_generators{'findmeth'}($method_reg, $decont_reg, 'defined');
                MAST::Call.new( :target($method_reg), :result($decont_reg), :flags([$Arg::obj]), $decont_reg);
                $regalloc.release_register($method_reg, $MVM_reg_obj);
            }

            %core_op_generators{
                # the conditional routines are reversed on purpose
                $op_name eq 'if' || $op_name eq 'with'
                  ?? 'unless_o' !! 'if_o'
            }(
                $decont_reg,
                ($operands == 3 ?? $else_lbl !! $end_lbl)
            );
            $regalloc.release_register($decont_reg, $MVM_reg_obj);
        }
        elsif @Full-width-coerce-to[@comp_ops[0].result_kind] -> $coerce-kind {
            # workaround for coercion unconditionally releasing the source register while we still need it later on
            my $coerce-reg := $regalloc.fresh_register: @comp_ops[0].result_kind;
            op_set($coerce-reg, @comp_ops[0].result_reg);
            my $il := MAST::InstructionList.new($coerce-reg, nqp::unbox_i(@comp_ops[0].result_kind));
            $qastcomp.coerce($il, $coerce-kind);
            %core_op_generators{
                $op_name eq 'if'
                  ?? @Negated-condition-op-kinds[@comp_ops[0].result_kind]
                  !! @Condition-op-kinds[        @comp_ops[0].result_kind]
            }(
                $il.result_reg,
                ($operands == 3 ?? $else_lbl !! $end_lbl)
            );
            $regalloc.release_register: $il.result_reg, $coerce-kind;
        }
        else {
            %core_op_generators{
                $op_name eq 'if'
                  ?? @Negated-condition-op-kinds[@comp_ops[0].result_kind]
                  !! @Condition-op-kinds[        @comp_ops[0].result_kind]
            }(
                @comp_ops[0].result_reg,
                ($operands == 3 ?? $else_lbl !! $end_lbl)
            );
        }

        # Emit the then, stash the result
        $*MAST_FRAME.insert_bytecode($then-subbuffer, nqp::elems($*MAST_FRAME.bytecode));

        if (!$is_void && nqp::unbox_i(@comp_ops[1].result_kind) != $res_kind) {
            # coercion will automatically release @comp_ops[1].result_reg
            my $coercion := $qastcomp.coercion(@comp_ops[1], $res_kind);
            op_set($res_reg, $coercion.result_reg);
        }
        elsif !$is_void {
            op_set($res_reg, @comp_ops[1].result_reg);
            $regalloc.release_register(@comp_ops[1].result_reg, nqp::unbox_i(@comp_ops[1].result_kind));
        }

        # Handle else branch (coercion of condition result if 2-arg).
        if $operands == 3 {
            # Terminate the then branch first.
            op_goto($end_lbl);
            $*MAST_FRAME.add-label($else_lbl);

            $*MAST_FRAME.insert_bytecode($else-subbuffer, nqp::elems($*MAST_FRAME.bytecode));

            if !$is_void {
                if nqp::unbox_i(@comp_ops[2].result_kind) != $res_kind {
                    # coercion will automatically release @comp_ops[2].result_reg
                    my $coercion := $qastcomp.coercion(@comp_ops[2], $res_kind);
                    op_set($res_reg, $coercion.result_reg);
                }
                else {
                    op_set($res_reg, @comp_ops[2].result_reg);
                    $regalloc.release_register(@comp_ops[2].result_reg, nqp::unbox_i(@comp_ops[2].result_kind));
                }
            }
        }

        unless $operands == 2 && !$is_void {
            # coercion will automatically release @comp_ops[0].result_reg
            $regalloc.release_register(@comp_ops[0].result_reg, nqp::unbox_i(@comp_ops[0].result_kind));
        }

        $*MAST_FRAME.add-label($end_lbl);

        MAST::InstructionList.new($res_reg, $res_kind)
    });
}

QAST::MASTOperations.add_core_op('defor', -> $qastcomp, $op {
    if nqp::elems($op.list) != 2 {
        nqp::die("The 'defor' op needs 2 operands, got " ~ nqp::elems($op.list));
    }

    # Compile the expression.
    my $regalloc := $*REGALLOC;
    my $res_reg := $regalloc.fresh_o();
    my $expr := $qastcomp.as_mast($op[0], :want($MVM_reg_obj));

    # Emit defined check.
    my $def_reg := $regalloc.fresh_i();
    my $lbl := MAST::Label.new();
    op_set($res_reg, $expr.result_reg);
    %core_op_generators{'isconcrete'}($def_reg, $res_reg);
    %core_op_generators{'if_i'}($def_reg, $lbl);
    $regalloc.release_register($def_reg, $MVM_reg_int64);

    # Emit "then" part.
    my $then := $qastcomp.as_mast($op[1], :want($MVM_reg_obj));
    $regalloc.release_register($expr.result_reg, $MVM_reg_obj);
    $expr.append($then);
    op_set($res_reg, $then.result_reg);
    $*MAST_FRAME.add-label($lbl);
    $regalloc.release_register($then.result_reg, $MVM_reg_obj);
    my $newer := MAST::InstructionList.new($res_reg, $MVM_reg_obj);
    $expr.append($newer);

    $expr
});

QAST::MASTOperations.add_core_op('xor', -> $qastcomp, $op {
    my int $res_kind   := $MVM_reg_obj;
    my $res_reg    := $*REGALLOC.fresh_o();
    my $t          := $*REGALLOC.fresh_i();
    my $u          := $*REGALLOC.fresh_i();
    my $d          := $*REGALLOC.fresh_o();
    my $falselabel := MAST::Label.new();
    my $endlabel   := MAST::Label.new();

    my @comp_ops;
    my $f;
    for $op.list {
        if $_.named eq 'false' {
            $f := $_;
        }
        else {
            nqp::push(@comp_ops, $_);
        }
    }

    my $apost := $qastcomp.as_mast(nqp::shift(@comp_ops), :want($MVM_reg_obj));
    op_set($res_reg, $apost.result_reg);
    op_decont($d, $apost.result_reg);
    %core_op_generators{'istrue'}($t, $d);
    $*REGALLOC.release_register($apost.result_reg, $MVM_reg_obj);

    my $have_middle_child := 1;
    my $bpost;
    while $have_middle_child {
        $bpost := $qastcomp.as_mast(nqp::shift(@comp_ops), :want($MVM_reg_obj));
        op_decont($d, $bpost.result_reg);
        %core_op_generators{'istrue'}($u, $d);

        my $jumplabel := MAST::Label.new();
        %core_op_generators{'unless_i'}($t, $jumplabel);
        %core_op_generators{'unless_i'}($u, $jumplabel);
        op_goto($falselabel);
        $*MAST_FRAME.add-label($jumplabel);

        if @comp_ops {
            my $truelabel := MAST::Label.new();
            %core_op_generators{'if_i'}($t, $truelabel);
            op_set($res_reg, $bpost.result_reg);
            $*REGALLOC.release_register($bpost.result_reg, $MVM_reg_obj);
            op_set($t, $u);
            $*MAST_FRAME.add-label($truelabel);
        }
        else {
            $have_middle_child := 0;
        }
    }
    $*REGALLOC.release_register($u, $MVM_reg_int64);

    %core_op_generators{'if_i'}($t, $endlabel);
    $*REGALLOC.release_register($t, $MVM_reg_int64);
    op_set($res_reg, $bpost.result_reg);
    $*REGALLOC.release_register($bpost.result_reg, $MVM_reg_obj);
    op_goto($endlabel);
    $*MAST_FRAME.add-label($falselabel);

    if $f {
        my $f_ast := $qastcomp.as_mast($f, :want($MVM_reg_obj));
        op_set($res_reg, $f_ast.result_reg);
        $*REGALLOC.release_register($f_ast.result_reg, $MVM_reg_obj);
    }
    else {
        op_null($res_reg);
    }

    $*MAST_FRAME.add-label($endlabel);

    $*REGALLOC.release_register($d, $MVM_reg_obj);

    MAST::InstructionList.new($res_reg, $res_kind)
});

QAST::MASTOperations.add_core_op('ifnull', -> $qastcomp, $op {
    if nqp::elems($op.list) != 2 {
        nqp::die("The 'ifnull' op needs 2 operands, got " ~ nqp::elems($op.list));
    }

    # Compile the expression.
    my $regalloc := $*REGALLOC;
    my $res_reg := $regalloc.fresh_o();
    my $expr := $qastcomp.as_mast($op[0], :want($MVM_reg_obj));

    # Emit null check.
    my $lbl := MAST::Label.new();
    op_set($res_reg, $expr.result_reg);
    %core_op_generators{'ifnonnull'}($expr.result_reg, $lbl);

    # Emit "then" part.
    my $then := $qastcomp.as_mast($op[1], :want($MVM_reg_obj));
    $regalloc.release_register($expr.result_reg, $MVM_reg_obj);
    $expr.append($then);
    op_set($res_reg, $then.result_reg);
    $*MAST_FRAME.add-label($lbl);
    $regalloc.release_register($then.result_reg, $MVM_reg_obj);
    my $newer := MAST::InstructionList.new($res_reg, $MVM_reg_obj);
    $expr.append($newer);

    $expr
});

sub loop_body($res_reg, $repness, $cond_temp, $redo_lbl, $test_lbl, @children, $orig_type, $regalloc, $op_name, $done_lbl, $qastcomp, $next_lbl, $res_kind) {
    # Generate a lousy return value for our while loop.
    unless $res_reg =:= MAST::VOID {
        op_null($res_reg);
    }

    if $repness {
        # It's a repeat_ variant, need to go straight into the
        # loop body unconditionally.
        #if $cond_temp {
        #    op_null($*BLOCK.local($cond_temp));
        #}
        op_goto($redo_lbl);
    }
    $*MAST_FRAME.add-label($test_lbl);

    # Compile each of the children.
    my @comp_ops;
    my @comp_types;

    my $comp := $qastcomp.as_mast(@children[0]);
    @comp_ops.push($comp);
    @comp_types.push($comp.result_kind);

    # Check operand count.
    my $operands := +@children;
    nqp::die("The '$repness$op_name' op needs 2 or 3 operands, got $operands")
        if $operands != 2 && $operands != 3;

    if @comp_ops[0].result_kind == $MVM_reg_obj {
        my $decont_reg := $regalloc.fresh_register($MVM_reg_obj);
        op_decont($decont_reg, @comp_ops[0].result_reg);
        %core_op_generators{
            # the conditional routines are reversed on purpose
            $op_name eq 'while' ?? 'unless_o' !! 'if_o'
        }(
            $decont_reg,
            $done_lbl
        );
        $regalloc.release_register($decont_reg, $MVM_reg_obj);
    }
    elsif @Full-width-coerce-to[@comp_ops[0].result_kind]
    -> $coerce-kind {
        my $coerce-reg := $regalloc.fresh_register: $coerce-kind;
        %core_op_generators{
            $op_name eq 'while'
              ?? @Negated-condition-op-kinds[@comp_ops[0].result_kind]
              !! @Condition-op-kinds[        @comp_ops[0].result_kind]
        }(
            $coerce-reg,
            $done_lbl
        );
        $regalloc.release_register: $coerce-reg, $coerce-kind;
    }
    else {
        %core_op_generators{
            $op_name eq 'while'
              ?? @Negated-condition-op-kinds[@comp_ops[0].result_kind]
              !! @Condition-op-kinds[        @comp_ops[0].result_kind]
        }(
            @comp_ops[0].result_reg,
            $done_lbl
        );
    }

    $*MAST_FRAME.add-label($redo_lbl);
    %core_op_generators{'osrpoint'}();

    # Emit the loop body; stash the result.

    $comp := $qastcomp.as_mast(@children[1], :want($MVM_reg_void));
    @comp_ops.push($comp);
    @comp_types.push($comp.result_kind);

    if $orig_type {
        @children[1][0].blocktype($orig_type);
    }
    my $body := $qastcomp.coerce(@comp_ops[1], $res_kind);

    # If there's a third child, evaluate it as part of the
    # "next".
    if $operands == 3 {
        $*MAST_FRAME.add-label($next_lbl);
        $comp := $qastcomp.as_mast(@children[2], :want($MVM_reg_void));
        @comp_ops.push($comp);
        @comp_types.push($comp.result_kind);
    }

    # Emit the iteration jump.
    op_goto($test_lbl);
}

# Loops.
for ('', 'repeat_') -> $repness {
    for <while until> -> $op_name {
        QAST::MASTOperations.add_core_op("$repness$op_name", -> $qastcomp, $op {
            # Create labels.
            my $while_id := $qastcomp.unique($op_name);
            my $test_lbl := MAST::Label.new();
            my $next_lbl := MAST::Label.new();
            my $redo_lbl := MAST::Label.new();
            my $done_lbl := MAST::Label.new();

            # Pick out applicable children; detect no handler case and munge
            # immediate arg case.
            my @children;
            my $handler := 1;
            my $orig_type;
            my $label_wval;
            my $cond_temp;
            for $op.list {
                if $_.named eq 'nohandler' { $handler := 0; }
                elsif $_.named eq 'label' { $label_wval := $_; }
                else { nqp::push(@children, $_) }
            }
            if needs_cond_passed(@children[1]) {
                $cond_temp := $qastcomp.unique('__im_cond_');
                @children[0] := QAST::Op.new(
                    :op('bind'),
                    QAST::Var.new( :name($cond_temp), :scope('local'), :decl('var') ),
                    @children[0]);
                $orig_type := @children[1].blocktype;
                @children[1].blocktype('declaration');
                @children[1] := QAST::Op.new(
                    :op('call'),
                    @children[1],
                    QAST::Var.new( :name($cond_temp), :scope('local') ));
            }

            # Allocate result register if needed.
            my $regalloc := $*REGALLOC;
            my int $res_kind := $MVM_reg_obj;
            my $res_reg;
            if nqp::defined($*WANT) && $*WANT == $MVM_reg_void {
                $res_kind := $MVM_reg_void;
                $res_reg := MAST::VOID;
            } else {
                $res_reg := $regalloc.fresh_register($res_kind);
            }

            # Test the condition and jump to the loop end if it's
            # not met.
            my $loop_start := nqp::elems($*MAST_FRAME.bytecode);

            # Emit postlude, with exception handlers if needed. Note that we
            # don't actually need to emit a bunch of handlers; since a handler
            # scope will happily throw control to a label of our choosing, we
            # just have the goto label be the place the control exception
            # needs to send control to.
            if $handler {
                my $lablocal;
                my $redo_mask := $HandlerCategory::redo;
                my $next_mask := $HandlerCategory::next;
                my $last_mask := $HandlerCategory::last;
                if $label_wval {
                    $redo_mask  := $redo_mask + $HandlerCategory::labeled;
                    $next_mask  := $next_mask + $HandlerCategory::labeled;
                    $last_mask  := $last_mask + $HandlerCategory::labeled;
                    my $labmast := $qastcomp.as_mast($label_wval, :want($MVM_reg_obj)); #nqp::where($label.value);
                    my $labreg  := $labmast.result_reg;
                    $lablocal   := MAST::Local.new(:index($*MAST_FRAME.add_local(NQPMu)));
                    op_set($lablocal, $labreg);
                    $regalloc.release_register($labreg, $MVM_reg_obj);
                }
                loop_body($res_reg, $repness, $cond_temp, $redo_lbl, $test_lbl, @children, $orig_type, $regalloc, $op_name, $done_lbl, $qastcomp, $next_lbl, $res_kind);
                MAST::HandlerScope.new(
                    :start($loop_start),
                    :category_mask($redo_mask),
                    :action($HandlerAction::unwind_and_goto),
                    :goto($redo_lbl),
                    :label($lablocal)
                );
                my $operands := +@children;
                MAST::HandlerScope.new(
                    :start($loop_start),
                    :category_mask($next_mask),
                    :action($HandlerAction::unwind_and_goto),
                    :goto($operands == 3 ?? $next_lbl !! $test_lbl),
                    :label($lablocal)
                );
                MAST::HandlerScope.new(
                    :start($loop_start),
                    :category_mask($last_mask),
                    :action($HandlerAction::unwind_and_goto),
                    :goto($done_lbl),
                    :label($lablocal)
                );
                $*MAST_FRAME.add-label($done_lbl);
                MAST::InstructionList.new($res_reg, $res_kind)
            }
            else {
                loop_body($res_reg, $repness, $cond_temp, $redo_lbl, $test_lbl, @children, $orig_type, $regalloc, $op_name, $done_lbl, $qastcomp, $next_lbl, $res_kind);
                $*MAST_FRAME.add-label($done_lbl);
                MAST::InstructionList.new($res_reg, $res_kind)
            }
        });
    }
}

sub for_loop_body($lbl_next, $iter_tmp, $lbl_done, @operands, $regalloc, $lbl_redo, $block_res, @val_temps) {
    # Emit loop test.
    $*MAST_FRAME.add-label($lbl_next);
    %core_op_generators{'unless_o'}($iter_tmp, $lbl_done);

    # Fetch values into temporaries (on the stack ain't enough in case
    # of redo).
    my @arg_flags;
    my $arity := @operands[1].arity || 1;
    while $arity > 0 {
        my $tmp := $regalloc.fresh_o();
        %core_op_generators{'shift_o'}($tmp, $iter_tmp);
        nqp::push(@val_temps, $tmp);
        nqp::push(@arg_flags, $Arg::obj);
        $arity := $arity - 1;
    }

    $*MAST_FRAME.add-label($lbl_redo);
    %core_op_generators{'osrpoint'}();

    # Now do block invocation.
    my $inv_il := MAST::Call.new(
        :target($block_res.result_reg),
        :flags(@arg_flags),
        |@val_temps
    );
    $inv_il := MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);

    # Emit next.
    op_goto($lbl_next );
    $regalloc.release_register($inv_il.result_reg, $inv_il.result_kind);
}

QAST::MASTOperations.add_core_op('for', -> $qastcomp, $op {
    my $handler := 1;
    my @operands;
    my $label_wval;
    for $op.list {
        if $_.named eq 'nohandler' { $handler := 0; }
        elsif $_.named eq 'label' { $label_wval := $_; }
        else { @operands.push($_) }
    }

    if nqp::elems(@operands) != 2 {
        nqp::die("The 'for' op needs 2 operands, got " ~ nqp::elems(@operands));
    }
    unless nqp::istype(@operands[1], QAST::Block) {
        nqp::die("The 'for' op expects a block as its second operand, got " ~ @operands[1].HOW.name(@operands[1]));
    }

    my $orig_blocktype := @operands[1].blocktype;

    if @operands[1].blocktype eq 'immediate' {
        @operands[1].blocktype('declaration');
    }
    elsif @operands[1].blocktype eq 'immediate_static' {
        @operands[1].blocktype('declaration_static');
    }

    # Evaluate the thing we'll iterate over, get the iterator and
    # store it in a temporary.
    my $regalloc := $*REGALLOC;
    my $list_il := $qastcomp.as_mast(@operands[0], :want($MVM_reg_obj));
    my $iter_tmp := $regalloc.fresh_o();
    %core_op_generators{'iter'}($iter_tmp, $list_il.result_reg);

    # Do similar for the block.
    my $block_res := $qastcomp.as_mast(@operands[1], :want($MVM_reg_obj));

    # Some labels we'll need.
    my $for_id := $qastcomp.unique('for');
    my $lbl_next := MAST::Label.new();
    my $lbl_redo := MAST::Label.new();
    my $lbl_done := MAST::Label.new();

    my @val_temps;

    # Emit postlude, wrapping in handlers if needed.
    if $handler {
        my $lablocal;
        my $redo_mask := $HandlerCategory::redo;
        my $next_mask := $HandlerCategory::next;
        my $last_mask := $HandlerCategory::last;
        if $label_wval {
            $redo_mask  := $redo_mask + $HandlerCategory::labeled;
            $next_mask  := $next_mask + $HandlerCategory::labeled;
            $last_mask  := $last_mask + $HandlerCategory::labeled;
            my $labmast := $qastcomp.as_mast($label_wval, :want($MVM_reg_obj));
            my $labreg  := $labmast.result_reg;
            $lablocal   := MAST::Local.new(:index($*MAST_FRAME.add_local(NQPMu)));
            op_set($lablocal, $labreg);
            $regalloc.release_register($labreg, $MVM_reg_obj);
        }
        my $loop_start := nqp::elems($*MAST_FRAME.bytecode);
        for_loop_body($lbl_next, $iter_tmp, $lbl_done, @operands, $regalloc, $lbl_redo, $block_res, @val_temps);
        MAST::HandlerScope.new(
            :start($loop_start),
            :category_mask($redo_mask),
            :action($HandlerAction::unwind_and_goto),
            :goto($lbl_redo),
            :label($lablocal)
        );
        MAST::HandlerScope.new(
            :start($loop_start),
            :category_mask($next_mask),
            :action($HandlerAction::unwind_and_goto),
            :goto($lbl_next),
            :label($lablocal)
        );
        MAST::HandlerScope.new(
            :start($loop_start),
            :category_mask($last_mask),
            :action($HandlerAction::unwind_and_goto),
            :goto($lbl_done),
            :label($lablocal)
        );
    }
    else {
        for_loop_body($lbl_next, $iter_tmp, $lbl_done, @operands, $regalloc, $lbl_redo, $block_res, @val_temps);
    }
    $*MAST_FRAME.add-label($lbl_done);

    @operands[1].blocktype($orig_blocktype);

    # Result; probably void, though evaluate to the input list if we must
    # give a value.
    $regalloc.release_register($block_res.result_reg, $block_res.result_kind);
    for @val_temps { $regalloc.release_register($_, $MVM_reg_obj) }
    if $*WANT == $MVM_reg_void {
        $regalloc.release_register($list_il.result_reg, $list_il.result_kind);
        MAST::InstructionList.new(MAST::VOID, $MVM_reg_void)
    }
    else {
        MAST::InstructionList.new($list_il.result_reg, $list_il.result_kind)
    }
});

# Calling
my @kind_to_args := [0,
    $Arg::int,  # $MVM_reg_int8            := 1;
    $Arg::int,  # $MVM_reg_int16           := 2;
    $Arg::int,  # $MVM_reg_int32           := 3;
    $Arg::int,  # $MVM_reg_int64           := 4;
    $Arg::num,  # $MVM_reg_num32           := 5;
    $Arg::num,  # $MVM_reg_num64           := 6;
    $Arg::str,  # $MVM_reg_str             := 7;
    $Arg::obj   # $MVM_reg_obj             := 8;
];

sub handle_arg($arg, $qastcomp, @arg_regs, @arg_flags, @arg_kinds) {
    # generate the code for the arg expression
    my $arg_mast := $qastcomp.as_mast($arg);
    my int $arg_mast_kind := $arg_mast.result_kind;
    if $arg_mast_kind == $MVM_reg_num32 {
        $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_num64);
    }
    elsif $arg_mast_kind == $MVM_reg_int32 || $arg_mast_kind == $MVM_reg_int16 ||
            $arg_mast_kind == $MVM_reg_int8 || $arg_mast_kind == $MVM_reg_uint64 ||
            $arg_mast_kind == $MVM_reg_uint32 || $arg_mast_kind == $MVM_reg_uint16 ||
            $arg_mast_kind == $MVM_reg_uint8 {
        $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_int64);
    }

    nqp::die("Arg expression cannot be void, cannot use the return of " ~ $arg.op)
        if $arg_mast.result_kind == $MVM_reg_void;

    nqp::die("Arg code did not result in a MAST::Local")
        unless $arg_mast.result_reg && $arg_mast.result_reg ~~ MAST::Local;

    nqp::push(@arg_kinds, $arg_mast.result_kind);


    # build up the typeflag
    my $result_typeflag := @kind_to_args[$arg_mast.result_kind];
    if nqp::can($arg, 'flat') && $arg.flat {
        if $arg.named {
            $result_typeflag := $result_typeflag +| $Arg::flatnamed;
        }
        else {
            $result_typeflag := $result_typeflag +| $Arg::flat;
        }
    }
    elsif nqp::can($arg, 'named') && $arg.named -> $name {
        # add in the extra arg for the name
        nqp::push(@arg_regs, $name);

        $result_typeflag := $result_typeflag +| $Arg::named;
    }

    # stash the result register and result typeflag
    nqp::push(@arg_regs, $arg_mast.result_reg);
    nqp::push(@arg_flags, $result_typeflag);
}

sub arrange_args(@in) {
    my @named := ();
    my @posit := ();
    for @in {
        nqp::push((nqp::can($_, 'named') && $_.named ?? @named !! @posit), $_);
    }
    for @named { nqp::push(@posit, $_) }
    @posit
}

my @kind_to_opcode := nqp::list_i;
nqp::bindpos_i(@kind_to_opcode, $MVM_reg_obj, %MAST::Ops::codes<arg_o>);
nqp::bindpos_i(@kind_to_opcode, $MVM_reg_str, %MAST::Ops::codes<arg_s>);
nqp::bindpos_i(@kind_to_opcode, $MVM_reg_int64, %MAST::Ops::codes<arg_i>);
nqp::bindpos_i(@kind_to_opcode, $MVM_reg_num64, %MAST::Ops::codes<arg_n>);
my $call_gen := sub ($qastcomp, $op) {
    # Work out what callee is.
    my $callee;
    my $return_type;
    my @args := $op.list;
    if $op.name {
        $callee := $qastcomp.as_mast(QAST::Op.new(
            :op('decont'),
            $op.op eq 'callstatic'
                ?? QAST::VM.new( :moarop('getlexstatic_o'), QAST::SVal.new( :value($op.name) ) )
                !! QAST::Var.new( :name($op.name), :scope('lexical') )));
    }
    elsif nqp::elems(@args) {
        @args := nqp::clone(@args);
        my $callee_qast := @args.shift;
        my $no_decont := nqp::istype($callee_qast, QAST::Op) && $callee_qast.op eq 'speshresolve'
            || nqp::istype($callee_qast, QAST::WVal) && !nqp::iscont($callee_qast.value);
        $callee := $qastcomp.as_mast(
            $no_decont ?? $callee_qast !! QAST::Op.new( :op('decont'), $callee_qast ),
            :want($MVM_reg_obj));
        if $op.op eq 'nativeinvoke' {
            $return_type := $qastcomp.as_mast(@args.shift(), :want($MVM_reg_obj));
        }
    }
    else {
        nqp::die("No name for call and empty children list");
    }
    @args := arrange_args(@args);

    nqp::die("Callee code did not result in a MAST::Local")
        unless $callee.result_reg && $callee.result_reg ~~ MAST::Local;

    my $regalloc := $*REGALLOC;
    my $frame    := $*MAST_FRAME;
    my $bytecode := $frame.bytecode;

    # The arg's results
    my @arg_mast := nqp::list();

    # Process arguments.
    for @args -> $arg {
        my $arg_mast := $qastcomp.as_mast($arg);
        my int $arg_mast_kind := nqp::unbox_i($arg_mast.result_kind);
        if $arg_mast_kind == $MVM_reg_num32 {
            $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_num64);
        }
        elsif $arg_mast_kind == $MVM_reg_int32 || $arg_mast_kind == $MVM_reg_int16 ||
                $arg_mast_kind == $MVM_reg_int8 || $arg_mast_kind == $MVM_reg_uint64 ||
                $arg_mast_kind == $MVM_reg_uint32 || $arg_mast_kind == $MVM_reg_uint16 ||
                $arg_mast_kind == $MVM_reg_uint8 {
            $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_int64);
        }
        nqp::push(@arg_mast, $arg_mast);
    }

    my uint $callsite-id := $frame.callsites.get_callsite_id_from_args(@args, @arg_mast);
    my uint64 $bytecode_pos := nqp::elems($bytecode);

    nqp::writeuint($bytecode, $bytecode_pos, $op_code_prepargs, 5);
    nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $callsite-id, 5);
    $bytecode_pos := $bytecode_pos + 4;

    my $i := 0;
    my uint64 $arg_out_pos := 0;
    for @args -> $arg {
        if nqp::can($arg, 'named') && !$arg.flat && $arg.named -> $name {
            nqp::writeuint($bytecode, $bytecode_pos, $op_code_argconst_s, 5);
            nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $arg_out_pos++, 5);
            my uint $name_idx := $frame.add-string($name);
            nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $name_idx, 9);
            $bytecode_pos := $bytecode_pos + 8;
        }

        my $arg_mast := @arg_mast[$i++];
        my int $kind := nqp::unbox_i($arg_mast.result_kind);
        my uint64 $arg_opcode := nqp::atpos_i(@kind_to_opcode, $kind);
        nqp::die("Unhandled arg type $kind") unless $arg_opcode;
        nqp::writeuint($bytecode, $bytecode_pos, $arg_opcode, 5);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $arg_out_pos++, 5);
        my uint64 $res_index := nqp::unbox_u($arg_mast.result_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $res_index, 5);
        $bytecode_pos := $bytecode_pos + 6;

        $regalloc.release_register($arg_mast.result_reg, $kind);
    }

    # Release the callee's result register.
    $regalloc.release_register($callee.result_reg, $MVM_reg_obj);

    # Figure out result register type
    my %result;
    my $res_reg;
    my int $res_kind;
    my int $is_nativecall := $op.op eq 'nativeinvoke';
    if !$is_nativecall && nqp::defined($*WANT) && $*WANT == $MVM_reg_void {
        $res_reg := MAST::VOID;
        $res_kind := $MVM_reg_void;
    }
    else {
        $res_kind := $qastcomp.type_to_register_kind($op.returns);
        $res_reg := $regalloc.fresh_register($res_kind);
        %result<result> := $res_reg;
    }

    # Generate call.
    if $res_reg.isa(MAST::Local) { # We got a return value
        my @local_types := $frame.local_types;
        my uint $index := nqp::unbox_u($res_reg);
        if $index >= nqp::elems(@local_types) {
            nqp::die("MAST::Local index out of range");
        }
        my $op_name := $is_nativecall ?? 'nativeinvoke_' !! 'invoke_';
        my int $primspec := nqp::objprimspec(@local_types[$index]);
        if $primspec == 1 {
            $op_name := $op_name ~ 'i';
        }
        elsif $primspec == 2 {
            $op_name := $op_name ~ 'n';
        }
        elsif $primspec == 3 {
            $op_name := $op_name ~ 's';
        }
        elsif $primspec == 0 { # object
            $op_name := $op_name ~ 'o';
        }
        else {
            nqp::die('Invalid MAST::Local type ' ~ @local_types[$index] ~ ' for return value ' ~ $index);
        }
        my uint $op_code := %MAST::Ops::codes{$op_name};
        nqp::writeuint($bytecode, $bytecode_pos, $op_code, 5);
        my uint $res_index := nqp::unbox_u($res_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $res_index, 5);
        my uint $callee_res_index := nqp::unbox_u($callee.result_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $callee_res_index, 5);
    }
    else {
        nqp::writeuint($bytecode, $bytecode_pos, $op_code_invoke_v, 5);
        my uint $callee_res_index := nqp::unbox_u($callee.result_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $callee_res_index, 5);
    }

    if $is_nativecall {
        $bytecode.write_uint16($return_type.result_reg);
    }

    MAST::InstructionList.new($res_reg, $res_kind)
};
QAST::MASTOperations.add_core_op('call', $call_gen, :!inlinable);
QAST::MASTOperations.add_core_op('callstatic', $call_gen, :!inlinable);
QAST::MASTOperations.add_core_op('nativeinvoke', $call_gen, :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('getarg_i', 'getarg_i');

QAST::MASTOperations.add_core_op('callmethod', -> $qastcomp, $op {
    my @args := nqp::clone($op.list);
    if nqp::elems(@args) == 0 {
        nqp::die('Method call node requires at least one child');
    }
    # evaluate the invocant expression
    my $invocant_qast := @args.shift();
    my $invocant := $qastcomp.as_mast($invocant_qast, :want($MVM_reg_obj));
    my $methodname_expr;
    if $op.name {
        # great!
    }
    elsif nqp::elems(@args) >= 1 {
        $methodname_expr := @args.shift();
    }
    else {
        nqp::die("Method call must either supply a name or have a child node that evaluates to the name");
    }
    @args := arrange_args(@args);

    nqp::die("Invocant expression must be an object, got " ~ $invocant.result_kind)
        unless nqp::unbox_i($invocant.result_kind) == $MVM_reg_obj;

    nqp::die("Invocant code did not result in a MAST::Local")
        unless $invocant.result_reg && $invocant.result_reg ~~ MAST::Local;

    my $frame := $*MAST_FRAME;
    my $bytecode := $frame.bytecode;

    # The arg's results
    my @arg_mast := [$invocant];

    # Process arguments.
    for @args -> $arg {
        my $arg_mast := $qastcomp.as_mast($arg);
        my int $arg_mast_kind := nqp::unbox_i($arg_mast.result_kind);
        if $arg_mast_kind == $MVM_reg_num32 {
            $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_num64);
        }
        elsif $arg_mast_kind == $MVM_reg_int32 || $arg_mast_kind == $MVM_reg_int16 ||
                $arg_mast_kind == $MVM_reg_int8 || $arg_mast_kind == $MVM_reg_uint64 ||
                $arg_mast_kind == $MVM_reg_uint32 || $arg_mast_kind == $MVM_reg_uint16 ||
                $arg_mast_kind == $MVM_reg_uint8 {
            $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_int64);
        }
        nqp::push(@arg_mast, $arg_mast);
    }
    nqp::unshift(@args, $invocant_qast);

    # generate and emit findmethod code
    my $regalloc   := $*REGALLOC;
    my $callee_reg := $regalloc.fresh_o();

    # This will hold the 3rd argument to findmeth(_s) - the method name
    # either a MAST::SVal or an $MVM_reg_str
    my $method_name;
    if $op.name {
        $method_name := $op.name;
    }
    else {
        my $method_name_ilist := $qastcomp.as_mast($methodname_expr, :want($MVM_reg_str));
        $method_name := $method_name_ilist.result_reg;
    }

    # push the op that finds the method based on either the provided name
    # or the provided name-producing expression.
    my $decont_inv_reg := $regalloc.fresh_o();
    op_decont($decont_inv_reg, $invocant.result_reg);
    $op.name
        ?? %core_op_generators{'findmeth'}($callee_reg, $decont_inv_reg, $method_name)
        !! %core_op_generators{'findmeth_s'}($callee_reg, $decont_inv_reg, $method_name);
    $regalloc.release_register($decont_inv_reg, $MVM_reg_obj);

    # release the method name register if we used one
    $regalloc.release_register($method_name, $MVM_reg_str) unless $op.name;

    my uint $callsite-id := $frame.callsites.get_callsite_id_from_args(@args, @arg_mast);
    my uint64 $bytecode_pos := nqp::elems($bytecode);

    nqp::writeuint($bytecode, $bytecode_pos, $op_code_prepargs, 5);
    nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $callsite-id, 5);
    $bytecode_pos := $bytecode_pos + 4;

    my $i := 0;
    my uint64 $arg_out_pos := 0;
    for @args -> $arg {
        if nqp::can($arg, 'named') && !$arg.flat && $arg.named -> $name {
            nqp::writeuint($bytecode, $bytecode_pos, $op_code_argconst_s, 5);
            nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $arg_out_pos++, 5);
            my uint $name_idx := $frame.add-string($name);
            nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $name_idx, 9);
            $bytecode_pos := $bytecode_pos + 8;
        }

        my $arg_mast := @arg_mast[$i++];
        my int $kind := nqp::unbox_i($arg_mast.result_kind);
        my uint64 $arg_opcode := nqp::atpos_i(@kind_to_opcode, $kind);
        nqp::die("Unhandled arg type $kind") unless $arg_opcode;
        nqp::writeuint($bytecode, $bytecode_pos, $arg_opcode, 5);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $arg_out_pos++, 5);
        my uint64 $res_index := nqp::unbox_u($arg_mast.result_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $res_index, 5);
        $bytecode_pos := $bytecode_pos + 6;

        $regalloc.release_register($arg_mast.result_reg, $kind);
    }

    # release the callee register
    $regalloc.release_register($callee_reg, $MVM_reg_obj);

    # Figure out expected result register type
    my int $res_kind := $qastcomp.type_to_register_kind($op.returns);

    # and allocate a register for it. Probably reuse an arg's or the invocant's.
    my $res_reg := $regalloc.fresh_register($res_kind);

    # Generate call.
    if $res_reg.isa(MAST::Local) { # We got a return value
        my @local_types := $frame.local_types;
        my uint $index := nqp::unbox_u($res_reg);
        if $index >= nqp::elems(@local_types) {
            nqp::die("MAST::Local index out of range");
        }
        my int $primspec := nqp::objprimspec(@local_types[$index]);
        my uint $op_code;
        if $primspec == 1 {
            $op_code := $op_code_invoke_i;
        }
        elsif $primspec == 2 {
            $op_code := $op_code_invoke_n;
        }
        elsif $primspec == 3 {
            $op_code := $op_code_invoke_s;
        }
        elsif $primspec == 0 { # object
            $op_code := $op_code_invoke_o;
        }
        else {
            nqp::die('Invalid MAST::Local type ' ~ @local_types[$index] ~ ' for return value ' ~ $index);
        }
        nqp::writeuint($bytecode, $bytecode_pos, $op_code, 5);
        my uint $res_index := nqp::unbox_u($res_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $res_index, 5);
        my uint $callee_reg_index := nqp::unbox_u($callee_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $callee_reg_index, 5);
    }
    else {
        nqp::writeuint($bytecode, $bytecode_pos, $op_code_invoke_v, 5);
        my uint $callee_reg_index := nqp::unbox_u($callee_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $callee_reg_index, 5);
    }

    MAST::InstructionList.new($res_reg, $res_kind)
});

my &op_dispatch_v := %core_op_generators<dispatch_v>;
my &op_dispatch_i := %core_op_generators<dispatch_i>;
my &op_dispatch_n := %core_op_generators<dispatch_n>;
my &op_dispatch_s := %core_op_generators<dispatch_s>;
my &op_dispatch_o := %core_op_generators<dispatch_o>;
QAST::MASTOperations.add_core_op('dispatch', :!inlinable, -> $qastcomp, $op {
    # Obtain name of the dispatcher to use.
    my @args := nqp::clone($op.list);
    my $name_qast := nqp::shift(@args);
    unless nqp::istype($name_qast, QAST::SVal) {
        nqp::die('First node of dispatch op must be a constant string naming the dispatcher');
    }
    my str $dispatcher_name := $name_qast.value;

    # Compile arguments and form callsite.
    my @arg_mast;
    my @arg_idxs;
    my $regalloc := $*REGALLOC;
    my $frame := $*MAST_FRAME;
    for @args -> $arg {
        my $arg_mast := $qastcomp.as_mast($arg);
        my int $arg_mast_kind := nqp::unbox_i($arg_mast.result_kind);
        if $arg_mast_kind == $MVM_reg_num32 {
            $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_num64);
        }
        elsif $arg_mast_kind == $MVM_reg_int32 || $arg_mast_kind == $MVM_reg_int16 ||
                $arg_mast_kind == $MVM_reg_int8 || $arg_mast_kind == $MVM_reg_uint64 ||
                $arg_mast_kind == $MVM_reg_uint32 || $arg_mast_kind == $MVM_reg_uint16 ||
                $arg_mast_kind == $MVM_reg_uint8 {
            $arg_mast := $qastcomp.coerce($arg_mast, $MVM_reg_int64);
        }
        nqp::push(@arg_mast, $arg_mast);
        nqp::push(@arg_idxs, $arg_mast.result_reg);
    }
    my uint $callsite_id := $frame.callsites.get_callsite_id_from_args(@args, @arg_mast);

    # Emit the correct dispatch instruction, allocating a result register if
    # not in void context.
    my $res_reg;
    my int $res_kind;
    if nqp::defined($*WANT) && $*WANT == $MVM_reg_void {
        $res_reg := MAST::VOID;
        $res_kind := $MVM_reg_void;
        op_dispatch_v($dispatcher_name, $callsite_id, @arg_idxs);
    }
    else {
        $res_kind := $qastcomp.type_to_register_kind($op.returns);
        $res_reg := $regalloc.fresh_register($res_kind);
        if $res_kind == $MVM_reg_obj {
            op_dispatch_o($res_reg, $dispatcher_name, $callsite_id, @arg_idxs);
        }
        elsif $res_kind == $MVM_reg_int64 {
            op_dispatch_i($res_reg, $dispatcher_name, $callsite_id, @arg_idxs);
        }
        elsif $res_kind == $MVM_reg_num64 {
            op_dispatch_n($res_reg, $dispatcher_name, $callsite_id, @arg_idxs);
        }
        elsif $res_kind == $MVM_reg_str {
            op_dispatch_s($res_reg, $dispatcher_name, $callsite_id, @arg_idxs);
        }
        else {
            nqp::die('Unsupported register return kind for dispatch op');
        }
    }

    # Free argument registers.
    for @arg_mast -> $arg_mast {
        $regalloc.release_register($arg_mast.result_reg, $arg_mast.result_kind);
    }

    MAST::InstructionList.new($res_reg, $res_kind)
});

# Binding
QAST::MASTOperations.add_core_op('bind', -> $qastcomp, $op {
    # Sanity checks.
    my @children := $op.list;
    if nqp::elems(@children) != 2 {
        nqp::die("The 'bind' op needs 2 children, got " ~ +@children);
    }
    unless nqp::istype(@children[0], QAST::Var) {
        nqp::die("First child of a 'bind' op must be a QAST::Var, got " ~ @children[0].HOW.name(@children[0]));
    }

    # Set the QAST of the think we're to bind, then delegate to
    # the compilation of the QAST::Var to handle the rest.
    my $*BINDVAL := @children[1];
    $qastcomp.as_mast(@children[0])
});

# Exception handling/munging.
QAST::MASTOperations.add_core_moarop_mapping('die', 'die');
QAST::MASTOperations.add_core_moarop_mapping('die_s', 'die');
QAST::MASTOperations.add_core_moarop_mapping('exception', 'exception');
QAST::MASTOperations.add_core_moarop_mapping('getextype', 'getexcategory');
QAST::MASTOperations.add_core_moarop_mapping('setextype', 'bindexcategory', 1);
QAST::MASTOperations.add_core_moarop_mapping('getpayload', 'getexpayload');
QAST::MASTOperations.add_core_moarop_mapping('setpayload', 'bindexpayload', 1);
QAST::MASTOperations.add_core_moarop_mapping('getmessage', 'getexmessage');
QAST::MASTOperations.add_core_moarop_mapping('setmessage', 'bindexmessage', 1);
QAST::MASTOperations.add_core_moarop_mapping('newexception', 'newexception');
QAST::MASTOperations.add_core_moarop_mapping('backtracestrings', 'backtracestrings');
QAST::MASTOperations.add_core_moarop_mapping('backtrace', 'backtrace');
QAST::MASTOperations.add_core_moarop_mapping('throw', 'throwdyn');
QAST::MASTOperations.add_core_moarop_mapping('rethrow', 'rethrow');
QAST::MASTOperations.add_core_moarop_mapping('resume', 'resume');
QAST::MASTOperations.add_core_moarop_mapping('throwpayloadlex', 'throwpayloadlex', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('throwpayloadlexcaller', 'throwpayloadlexcaller', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('lastexpayload', 'lastexpayload');
QAST::MASTOperations.add_core_moarop_mapping('throwextype', 'throwcatdyn');

my %handler_names := nqp::hash(
    'CATCH',   $HandlerCategory::catch,
    'CONTROL', $HandlerCategory::control,
    'NEXT',    $HandlerCategory::next,
    'LAST',    $HandlerCategory::last,
    'REDO',    $HandlerCategory::redo,
    'TAKE',    $HandlerCategory::take,
    'WARN',    $HandlerCategory::warn,
    'PROCEED', $HandlerCategory::proceed,
    'SUCCEED', $HandlerCategory::succeed,
    'AWAIT',   $HandlerCategory::await,
    'EMIT',    $HandlerCategory::emit,
    'DONE',    $HandlerCategory::done,
    'RETURN',  $HandlerCategory::return,
);
QAST::MASTOperations.add_core_op('handle', :!inlinable, sub ($qastcomp, $op) {
    my @children := nqp::clone($op.list());
    if nqp::elems(@children) == 0 {
        nqp::die("The 'handle' op requires at least one child");
    }

    # If there's exactly one child, then there's nothing protecting
    # it; just compile it and we're done.
    my $protected := @children.shift();
    unless @children {
        return $qastcomp.as_mast($protected);
    }

    # Otherwise, we need to generate and install a handler block, which will
    # decide that to do by category.
    my $regalloc := $*REGALLOC;
    my $mask := 0;
    my $hblock := QAST::Block.new(
        QAST::Op.new(
            :op('bind'),
            QAST::Var.new( :name('__category__'), :scope('local'), :decl('var') ),
            QAST::Op.new(
                :op('getextype'),
                QAST::Op.new( :op('exception') )
            )));
    my $push_target := $hblock;
    my $lablocal;
    for @children -> $type, $handler {
        if $type eq 'LABELED' {
            $mask       := $HandlerCategory::labeled;
            my $labmast := $qastcomp.as_mast($handler, :want($MVM_reg_obj));
            my $labreg  := $labmast.result_reg;
            $lablocal   := MAST::Local.new(:index($*MAST_FRAME.add_local(NQPMu)));
            op_set($lablocal, $labreg);
            $regalloc.release_register($labreg, $MVM_reg_obj);
        }
        else {
            # Get the category mask.
            unless nqp::existskey(%handler_names, $type) {
                nqp::die("Invalid handler type '$type'");
            }
            my $cat_mask := $type eq 'CONTROL' ?? 0xEFFE !! %handler_names{$type};

            # Chain in this handler.
            my $check := QAST::Op.new(
                    :op('if'),
                    QAST::Op.new(
                        :op('bitand_i'),
                        QAST::Var.new( :name('__category__'), :scope('local') ),
                        QAST::IVal.new( :value($cat_mask) )
                    ),
                    $handler
                );
            # Push this check as the 3rd arg to op 'if' in case this is not the first iteration.
            $push_target.push($check);
            $push_target := $check;

            # Add to mask.
            $mask := nqp::bitor_i($mask, $cat_mask);
        }
    }

    # Add a local and store the handler block into it.
    my $hblocal := MAST::Local.new(:index($*MAST_FRAME.add_local(NQPMu)));
    my $hbmast  := $qastcomp.as_mast($hblock, :want($MVM_reg_obj));
    op_set($hblocal, $hbmast.result_reg);
    $regalloc.release_register($hbmast.result_reg, $MVM_reg_obj);

    # Wrap instructions to try up in a handler and evaluate to the result
    # of the protected code of the exception handler.
    my $protected_result  := $regalloc.fresh_o();
    my $prot_start := nqp::elems($*MAST_FRAME.bytecode);
    my $protil := $qastcomp.as_mast($protected, :want($MVM_reg_obj));
    my $uwlbl  := MAST::Label.new();
    my $endlbl := MAST::Label.new();
    op_set($protected_result, $protil.result_reg);
    op_goto($endlbl);
    MAST::HandlerScope.new(
        :start($prot_start), :goto($uwlbl), :block($hblocal),
        :category_mask($mask), :action($HandlerAction::invoke_and_we'll_see),
        :label($lablocal));
    $*MAST_FRAME.add-label($uwlbl);
    %core_op_generators{'takehandlerresult'}($protected_result);
    $*MAST_FRAME.add-label($endlbl);

    $regalloc.release_register($protil.result_reg, $MVM_reg_obj);

    MAST::InstructionList.new($protected_result, $MVM_reg_obj)
});

# Simple payload handler.
QAST::MASTOperations.add_core_op('handlepayload', :!inlinable, sub ($qastcomp, $op) {
    my @children := $op.list;
    if nqp::elems(@children) != 3 {
        nqp::die("The 'handlepayload' op needs 3 children, got " ~ +@children);
    }
    my str $type := @children[1];
    unless nqp::existskey(%handler_names, $type) {
        nqp::die("Invalid handler type '$type'");
    }
    my int $mask := %handler_names{$type};

    my $prot_start := nqp::elems($*MAST_FRAME.bytecode);
    my $protected := $qastcomp.as_mast(@children[0], :want($MVM_reg_obj));
    my $endlbl     := MAST::Label.new();
    my $handlelbl  := MAST::Label.new();
    op_goto($endlbl);
    MAST::HandlerScope.new(
        :start($prot_start), :goto($handlelbl),
        :category_mask($mask), :action($HandlerAction::unwind_and_goto_with_payload));
    $*MAST_FRAME.add-label($handlelbl);
    my $handler   := $qastcomp.as_mast(@children[2], :want($MVM_reg_obj));
    op_set($protected.result_reg, $handler.result_reg);
    $*MAST_FRAME.add-label($endlbl);
    $*REGALLOC.release_register($handler.result_reg, $MVM_reg_obj);

    MAST::InstructionList.new($protected.result_reg, $MVM_reg_obj)
});

# Control exception throwing.
my %control_map := nqp::hash(
    'next', $HandlerCategory::next,
    'last', $HandlerCategory::last,
    'redo', $HandlerCategory::redo
);
QAST::MASTOperations.add_core_op('control', -> $qastcomp, $op {
    my $regalloc := $*REGALLOC;
    my $name := $op.name;
    my $label;
    for $op.list {
        $label := $_ if $_.named eq 'label';
    }

    if nqp::existskey(%control_map, $name) {
        if $label {
            # Create an exception object, and attach the label to its payload.
            my $res := $regalloc.fresh_register($MVM_reg_obj);
            my $ex  := $regalloc.fresh_register($MVM_reg_obj);
            my $lbl := $qastcomp.as_mast($label, :want($MVM_reg_obj));
            my $cat := $regalloc.fresh_register($MVM_reg_int64);
            my $il  := MAST::InstructionList.new($res, $MVM_reg_obj);
            $il.append($lbl);
            %core_op_generators{'newexception'}($ex);
            %core_op_generators{'bindexpayload'}($ex,  $lbl.result_reg );
            %core_op_generators{'const_i64'}($cat, nqp::add_i(%control_map{$name}, $HandlerCategory::labeled));
            %core_op_generators{'bindexcategory'}($ex,  $cat );
            %core_op_generators{'throwdyn'}($res, $ex);
            $il
        }
        else {
            my $res := $regalloc.fresh_register($MVM_reg_obj);
            %core_op_generators{'throwcatdyn'}($res, %control_map{$name});
            MAST::InstructionList.new($res, $MVM_reg_obj)
        }
    }
    else {
        nqp::die("Unknown control exception type '$name'");
    }
});

# Default ways to box/unbox (for no particular HLL).
QAST::MASTOperations.add_hll_unbox('', $MVM_reg_int64, -> $qastcomp, $reg {
    my $regalloc := $*REGALLOC;
    my $res_reg := $regalloc.fresh_register($MVM_reg_int64);
    $regalloc.release_register($reg, $MVM_reg_obj);
    my $dc := $regalloc.fresh_register($MVM_reg_obj);
    op_decont($dc, $reg);
    %core_op_generators{'smrt_intify'}($res_reg, $dc);
    $regalloc.release_register($dc, $MVM_reg_obj);
    MAST::InstructionList.new($res_reg, $MVM_reg_int64)
});
QAST::MASTOperations.add_hll_unbox('', $MVM_reg_num64, -> $qastcomp, $reg {
    my $regalloc := $*REGALLOC;
    my $res_reg := $regalloc.fresh_register($MVM_reg_num64);
    $regalloc.release_register($reg, $MVM_reg_obj);
    my $dc := $regalloc.fresh_register($MVM_reg_obj);
    op_decont($dc, $reg);
    %core_op_generators{'smrt_numify'}($res_reg, $dc);
    $regalloc.release_register($dc, $MVM_reg_obj);
    MAST::InstructionList.new($res_reg, $MVM_reg_num64)
});
QAST::MASTOperations.add_hll_unbox('', $MVM_reg_str, -> $qastcomp, $reg {
    my $regalloc := $*REGALLOC;
    my $res_reg := $regalloc.fresh_register($MVM_reg_str);
    $regalloc.release_register($reg, $MVM_reg_obj);
    my $dc := $regalloc.fresh_register($MVM_reg_obj);
    op_decont($dc, $reg);
    %core_op_generators{'smrt_strify'}($res_reg, $dc);
    $regalloc.release_register($dc, $MVM_reg_obj);
    MAST::InstructionList.new($res_reg, $MVM_reg_str)
});
QAST::MASTOperations.add_hll_unbox('', $MVM_reg_uint64, -> $qastcomp, $reg {
    my $regalloc := $*REGALLOC;
    my $a := $regalloc.fresh_register($MVM_reg_int64);
    my $b := $regalloc.fresh_register($MVM_reg_uint64);
    $regalloc.release_register($reg, $MVM_reg_obj);
    my $dc := $regalloc.fresh_register($MVM_reg_obj);
    op_decont($dc, $reg);
    %core_op_generators{'smrt_intify'}($a, $dc);
    %core_op_generators{'coerce_iu'}($b, $a);
    $regalloc.release_register($a, $MVM_reg_int64);
    $regalloc.release_register($dc, $MVM_reg_obj);
    MAST::InstructionList.new($b, $MVM_reg_int64)
});
sub boxer($kind, $type_op, $op) {
    -> $qastcomp, $reg {
        my $regalloc := $*REGALLOC;
        my $res_reg := $regalloc.fresh_register($MVM_reg_obj);
        %core_op_generators{$type_op}($res_reg);
        %core_op_generators{$op}($res_reg, $reg, $res_reg);
        $regalloc.release_register($reg, $kind);
        MAST::InstructionList.new($res_reg, $MVM_reg_obj)
    }
}
QAST::MASTOperations.add_hll_box('', $MVM_reg_int64, boxer($MVM_reg_int64, 'hllboxtype_i', 'box_i'));
QAST::MASTOperations.add_hll_box('', $MVM_reg_num64, boxer($MVM_reg_num64, 'hllboxtype_n', 'box_n'));
QAST::MASTOperations.add_hll_box('', $MVM_reg_str, boxer($MVM_reg_str, 'hllboxtype_s', 'box_s'));
QAST::MASTOperations.add_hll_box('', $MVM_reg_uint64, boxer($MVM_reg_uint64, 'hllboxtype_i', 'box_u'));
QAST::MASTOperations.add_hll_box('', $MVM_reg_void, -> $qastcomp, $reg {
    my $res_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
    op_null($res_reg);
    MAST::InstructionList.new($res_reg, $MVM_reg_obj)
});

# Context introspection
QAST::MASTOperations.add_core_moarop_mapping('ctx', 'ctx', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('ctxouter', 'ctxouter', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('ctxcaller', 'ctxcaller', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('ctxcode', 'ctxcode', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('ctxouterskipthunks', 'ctxouterskipthunks', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('ctxcallerskipthunks', 'ctxcallerskipthunks', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('curcode', 'curcode', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('callercode', 'callercode', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('ctxlexpad', 'ctxlexpad', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('curlexpad', 'ctx', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('lexprimspec', 'lexprimspec');

# Argument capture processing, for writing things like multi-dispatchers in
# high level languages.
QAST::MASTOperations.add_core_moarop_mapping('usecapture', 'usecapture', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('savecapture', 'savecapture', :!inlinable);
QAST::MASTOperations.add_core_moarop_mapping('captureposelems', 'captureposelems');
QAST::MASTOperations.add_core_moarop_mapping('captureposarg', 'captureposarg');
QAST::MASTOperations.add_core_moarop_mapping('captureposarg_i', 'captureposarg_i');
QAST::MASTOperations.add_core_moarop_mapping('captureposarg_n', 'captureposarg_n');
QAST::MASTOperations.add_core_moarop_mapping('captureposarg_s', 'captureposarg_s');
QAST::MASTOperations.add_core_moarop_mapping('captureposprimspec', 'captureposprimspec');
QAST::MASTOperations.add_core_moarop_mapping('captureexistsnamed', 'captureexistsnamed');
QAST::MASTOperations.add_core_moarop_mapping('capturehasnameds', 'capturehasnameds');
QAST::MASTOperations.add_core_moarop_mapping('capturenamedshash', 'capturenamedshash');
QAST::MASTOperations.add_core_moarop_mapping('objprimspec', 'objprimspec');
QAST::MASTOperations.add_core_moarop_mapping('objprimbits', 'objprimbits');
QAST::MASTOperations.add_core_moarop_mapping('objprimunsigned', 'objprimunsigned');

# Multiple dispatch related.
QAST::MASTOperations.add_core_moarop_mapping('invokewithcapture', 'invokewithcapture');
QAST::MASTOperations.add_core_moarop_mapping('multicacheadd', 'multicacheadd');
QAST::MASTOperations.add_core_moarop_mapping('multicachefind', 'multicachefind');

# Constant mapping.
my %const_map := nqp::hash(
    'CCLASS_ANY',           65535,
    'CCLASS_UPPERCASE',     1,
    'CCLASS_LOWERCASE',     2,
    'CCLASS_ALPHABETIC',    4,
    'CCLASS_NUMERIC',       8,
    'CCLASS_HEXADECIMAL',   16,
    'CCLASS_WHITESPACE',    32,
    'CCLASS_PRINTING',      64,
    'CCLASS_BLANK',         256,
    'CCLASS_CONTROL',       512,
    'CCLASS_PUNCTUATION',   1024,
    'CCLASS_ALPHANUMERIC',  2048,
    'CCLASS_NEWLINE',       4096,
    'CCLASS_WORD',          8192,

    'HLL_ROLE_NONE',        0,
    'HLL_ROLE_INT',         1,
    'HLL_ROLE_NUM',         2,
    'HLL_ROLE_STR',         3,
    'HLL_ROLE_ARRAY',       4,
    'HLL_ROLE_HASH',        5,
    'HLL_ROLE_CODE',        6,

    'CONTROL_ANY',          2,
    'CONTROL_NEXT',         4,
    'CONTROL_REDO',         8,
    'CONTROL_LAST',         16,
    'CONTROL_RETURN',       32,
    'CONTROL_TAKE',         128,
    'CONTROL_WARN',         256,
    'CONTROL_SUCCEED',      512,
    'CONTROL_PROCEED',      1024,
    'CONTROL_LABELED',      4096,
    'CONTROL_AWAIT',        8192,
    'CONTROL_EMIT',         16384,
    'CONTROL_DONE',         32768,

    'STAT_EXISTS',             0,
    'STAT_FILESIZE',           1,
    'STAT_ISDIR',              2,
    'STAT_ISREG',              3,
    'STAT_ISDEV',              4,
    'STAT_CREATETIME',         5,
    'STAT_ACCESSTIME',         6,
    'STAT_MODIFYTIME',         7,
    'STAT_CHANGETIME',         8,
    'STAT_BACKUPTIME',         9,
    'STAT_UID',                10,
    'STAT_GID',                11,
    'STAT_ISLNK',              12,
    'STAT_PLATFORM_DEV',       -1,
    'STAT_PLATFORM_INODE',     -2,
    'STAT_PLATFORM_MODE',      -3,
    'STAT_PLATFORM_NLINKS',    -4,
    'STAT_PLATFORM_DEVTYPE',   -5,
    'STAT_PLATFORM_BLOCKSIZE', -6,
    'STAT_PLATFORM_BLOCKS',    -7,

    'PIPE_INHERIT_IN',          1,
    'PIPE_IGNORE_IN',           2,
    'PIPE_CAPTURE_IN',          4,
    'PIPE_INHERIT_OUT',         8,
    'PIPE_IGNORE_OUT',          16,
    'PIPE_CAPTURE_OUT',         32,
    'PIPE_INHERIT_ERR',         64,
    'PIPE_IGNORE_ERR',          128,
    'PIPE_CAPTURE_ERR',         256,
    'PIPE_MERGED_OUT_ERR',      512,

    'TYPE_CHECK_CACHE_DEFINITIVE',  0,
    'TYPE_CHECK_CACHE_THEN_METHOD', 1,
    'TYPE_CHECK_NEEDS_ACCEPTS',     2,

    'C_TYPE_CHAR',              -1,
    'C_TYPE_SHORT',             -2,
    'C_TYPE_INT',               -3,
    'C_TYPE_LONG',              -4,
    'C_TYPE_LONGLONG',          -5,
    'C_TYPE_SIZE_T',            -6,
    'C_TYPE_BOOL',              -7,
    'C_TYPE_ATOMIC_INT',        -8,
    'C_TYPE_FLOAT',             -1,
    'C_TYPE_DOUBLE',            -2,
    'C_TYPE_LONGDOUBLE',        -3,

    'NORMALIZE_NONE',            0,
    'NORMALIZE_NFC',             1,
    'NORMALIZE_NFD',             2,
    'NORMALIZE_NFKC',            3,
    'NORMALIZE_NFKD',            4,

    'RUSAGE_UTIME_SEC',          0,
    'RUSAGE_UTIME_MSEC',         1,
    'RUSAGE_STIME_SEC',          2,
    'RUSAGE_STIME_MSEC',         3,
    'RUSAGE_MAXRSS',             4,
    'RUSAGE_IXRSS',              5,
    'RUSAGE_IDRSS',              6,
    'RUSAGE_ISRSS',              7,
    'RUSAGE_MINFLT',             8,
    'RUSAGE_MAJFLT',             9,
    'RUSAGE_NSWAP',              10,
    'RUSAGE_INBLOCK',            11,
    'RUSAGE_OUBLOCK',            12,
    'RUSAGE_MSGSND',             13,
    'RUSAGE_MSGRCV',             14,
    'RUSAGE_NSIGNALS',           15,
    'RUSAGE_NVCSW',              16,
    'RUSAGE_NIVCSW',             17,

    'UNAME_SYSNAME',              0,
    'UNAME_RELEASE',              1,
    'UNAME_VERSION',              2,
    'UNAME_MACHINE',              3,

    'MVM_OPERAND_LITERAL',        0,
    'MVM_OPERAND_READ_REG',       1,
    'MVM_OPERAND_WRITE_REG',      2,
    'MVM_OPERAND_READ_LEX',       3,
    'MVM_OPERAND_WRITE_LEX',      4,
    'MVM_OPERAND_RW_MASK',        7,

    'MVM_OPERAND_INT8',           8,
    'MVM_OPERAND_INT16',         16,
    'MVM_OPERAND_INT32',         24,
    'MVM_OPERAND_INT64',         32,
    'MVM_OPERAND_NUM32',         40,
    'MVM_OPERAND_NUM64',         48,
    'MVM_OPERAND_STR',           56,
    'MVM_OPERAND_OBJ',           64,
    'MVM_OPERAND_INS',           72,
    'MVM_OPERAND_TYPE_VAR',      80,
    'MVM_OPERAND_LEX_OUTER',     88,
    'MVM_OPERAND_CODEREF',       96,
    'MVM_OPERAND_CALLSITE',     104,
    'MVM_OPERAND_TYPE_MASK',    248,
    'MVM_OPERAND_UINT8',        136,
    'MVM_OPERAND_UINT16',       144,
    'MVM_OPERAND_UINT32',       152,
    'MVM_OPERAND_UINT64',       160,

    'BINARY_ENDIAN_NATIVE',       0,
    'BINARY_ENDIAN_LITTLE',       1,
    'BINARY_ENDIAN_BIG',          2,

    'BINARY_SIZE_8_BIT',          0,
    'BINARY_SIZE_16_BIT',         4,
    'BINARY_SIZE_32_BIT',         8,
    'BINARY_SIZE_64_BIT',        12,

    'SOCKET_FAMILY_UNSPEC',       0,
    'SOCKET_FAMILY_INET',         1,
    'SOCKET_FAMILY_INET6',        2,
    'SOCKET_FAMILY_UNIX',         3,
);
QAST::MASTOperations.add_core_op('const', -> $qastcomp, $op {
    if nqp::existskey(%const_map, $op.name) {
        $qastcomp.as_mast(QAST::IVal.new( :value(%const_map{$op.name}) ))
    }
    else {
        nqp::die("Unknown constant '" ~ $op.name ~ "'");
    }
});

# Default way to do positional and associative lookups.
QAST::MASTOperations.add_core_moarop_mapping('positional_get', 'atpos_o');
QAST::MASTOperations.add_core_moarop_mapping('positional_bind', 'bindpos_o', 2);
QAST::MASTOperations.add_core_moarop_mapping('associative_get', 'atkey_o');
QAST::MASTOperations.add_core_moarop_mapping('associative_bind', 'bindkey_o', 2);

# I/O opcodes
QAST::MASTOperations.add_core_moarop_mapping('say', 'say', 0);
QAST::MASTOperations.add_core_moarop_mapping('print', 'print', 0);
QAST::MASTOperations.add_core_moarop_mapping('stat', 'stat');
QAST::MASTOperations.add_core_moarop_mapping('stat_time', 'stat_time');
QAST::MASTOperations.add_core_moarop_mapping('lstat', 'lstat');
QAST::MASTOperations.add_core_moarop_mapping('lstat_time', 'lstat_time');
QAST::MASTOperations.add_core_moarop_mapping('open', 'open_fh');
QAST::MASTOperations.add_core_moarop_mapping('filereadable', 'filereadable');
QAST::MASTOperations.add_core_moarop_mapping('filewritable', 'filewritable');
QAST::MASTOperations.add_core_moarop_mapping('fileexecutable', 'fileexecutable');
QAST::MASTOperations.add_core_op('fileislink', -> $qastcomp, $op {
    $qastcomp.as_mast( QAST::Op.new( :op('stat'), $op[0], QAST::IVal.new( :value(12) )) )
});
QAST::MASTOperations.add_core_moarop_mapping('flushfh', 'sync_fh');
QAST::MASTOperations.add_core_moarop_mapping('getstdin', 'getstdin');
QAST::MASTOperations.add_core_moarop_mapping('getstdout', 'getstdout');
QAST::MASTOperations.add_core_moarop_mapping('getstderr', 'getstderr');
QAST::MASTOperations.add_core_moarop_mapping('tellfh', 'tell_fh');
QAST::MASTOperations.add_core_moarop_mapping('seekfh', 'seek_fh');
QAST::MASTOperations.add_core_moarop_mapping('lockfh', 'lock_fh');
QAST::MASTOperations.add_core_moarop_mapping('unlockfh', 'unlock_fh');
QAST::MASTOperations.add_core_moarop_mapping('readfh', 'read_fhb', 1);
QAST::MASTOperations.add_core_moarop_mapping('writefh', 'write_fhb', 1);
QAST::MASTOperations.add_core_moarop_mapping('eoffh', 'eof_fh');
QAST::MASTOperations.add_core_moarop_mapping('closefh', 'close_fh', 0);
QAST::MASTOperations.add_core_moarop_mapping('isttyfh', 'istty_fh');
QAST::MASTOperations.add_core_moarop_mapping('filenofh', 'fileno_fh');
QAST::MASTOperations.add_core_moarop_mapping('socket', 'socket');
QAST::MASTOperations.add_core_moarop_mapping('connect', 'connect_sk', 0);
QAST::MASTOperations.add_core_moarop_mapping('bindsock', 'bind_sk', 0);
QAST::MASTOperations.add_core_moarop_mapping('accept', 'accept_sk');
QAST::MASTOperations.add_core_moarop_mapping('getport', 'getport_sk');
QAST::MASTOperations.add_core_moarop_mapping('setbuffersizefh', 'setbuffersize_fh', 0);

QAST::MASTOperations.add_core_moarop_mapping('chmod', 'chmod_f', 0);
QAST::MASTOperations.add_core_moarop_mapping('unlink', 'delete_f', 0);
QAST::MASTOperations.add_core_moarop_mapping('rmdir', 'rmdir', 0);
QAST::MASTOperations.add_core_moarop_mapping('cwd', 'cwd');
QAST::MASTOperations.add_core_moarop_mapping('chdir', 'chdir', 0);
QAST::MASTOperations.add_core_moarop_mapping('mkdir', 'mkdir', 0);
QAST::MASTOperations.add_core_moarop_mapping('rename', 'rename_f', 0);
QAST::MASTOperations.add_core_moarop_mapping('copy', 'copy_f', 0);
QAST::MASTOperations.add_core_moarop_mapping('symlink', 'symlink');
QAST::MASTOperations.add_core_moarop_mapping('readlink', 'readlink');
QAST::MASTOperations.add_core_moarop_mapping('link', 'link');
QAST::MASTOperations.add_core_moarop_mapping('opendir', 'open_dir');
QAST::MASTOperations.add_core_moarop_mapping('nextfiledir', 'read_dir');
QAST::MASTOperations.add_core_moarop_mapping('closedir', 'close_dir');
QAST::MASTOperations.add_core_op('sprintf', -> $qastcomp, $op {
    my @operands := $op.list;
    $qastcomp.as_mast(
        QAST::Op.new(
            :op('call'),
            :returns(str),
            QAST::Op.new(
                :op('gethllsym'),
                QAST::SVal.new( :value('nqp') ),
                QAST::SVal.new( :value('sprintf') )
            ),
            |@operands )
    );
});
QAST::MASTOperations.add_core_op('sprintfdirectives', -> $qastcomp, $op {
    my @operands := $op.list;
    $qastcomp.as_mast(
        QAST::Op.new(
            :op('call'),
            :returns(int),
            QAST::Op.new(
                :op('gethllsym'),
                QAST::SVal.new( :value('nqp') ),
                QAST::SVal.new( :value('sprintfdirectives') )
            ),
            |@operands )
    );
});
QAST::MASTOperations.add_core_op('sprintfaddargumenthandler', -> $qastcomp, $op {
    my @operands := $op.list;
    $qastcomp.as_mast(
        QAST::Op.new(
            :op('call'),
            :returns(str),
            QAST::Op.new(
                :op('gethllsym'),
                QAST::SVal.new( :value('nqp') ),
                QAST::SVal.new( :value('sprintfaddargumenthandler') )
            ),
            |@operands )
    );
});

# terms
QAST::MASTOperations.add_core_moarop_mapping('time_i', 'time_i');
QAST::MASTOperations.add_core_moarop_mapping('time_n', 'time_n');

# Arithmetic ops
QAST::MASTOperations.add_core_moarop_mapping('add_i', 'add_i');
QAST::MASTOperations.add_core_moarop_mapping('add_I', 'add_I');
QAST::MASTOperations.add_core_moarop_mapping('add_n', 'add_n');
QAST::MASTOperations.add_core_moarop_mapping('sub_i', 'sub_i');
QAST::MASTOperations.add_core_moarop_mapping('sub_I', 'sub_I');
QAST::MASTOperations.add_core_moarop_mapping('sub_n', 'sub_n');
QAST::MASTOperations.add_core_moarop_mapping('mul_i', 'mul_i');
QAST::MASTOperations.add_core_moarop_mapping('mul_I', 'mul_I');
QAST::MASTOperations.add_core_moarop_mapping('mul_n', 'mul_n');
QAST::MASTOperations.add_core_moarop_mapping('div_i', 'div_i');
QAST::MASTOperations.add_core_moarop_mapping('div_I', 'div_I');
QAST::MASTOperations.add_core_moarop_mapping('div_In', 'div_In');
QAST::MASTOperations.add_core_moarop_mapping('div_n', 'div_n');
QAST::MASTOperations.add_core_moarop_mapping('mod_i', 'mod_i');
QAST::MASTOperations.add_core_moarop_mapping('mod_I', 'mod_I');
QAST::MASTOperations.add_core_moarop_mapping('expmod_I', 'expmod_I');
QAST::MASTOperations.add_core_moarop_mapping('mod_n', 'mod_n');
QAST::MASTOperations.add_core_moarop_mapping('neg_i', 'neg_i');
QAST::MASTOperations.add_core_moarop_mapping('neg_I', 'neg_I');
QAST::MASTOperations.add_core_moarop_mapping('neg_n', 'neg_n');
QAST::MASTOperations.add_core_moarop_mapping('pow_i', 'pow_i');
QAST::MASTOperations.add_core_moarop_mapping('pow_I', 'pow_I');
QAST::MASTOperations.add_core_moarop_mapping('pow_n', 'pow_n');
QAST::MASTOperations.add_core_moarop_mapping('abs_i', 'abs_i');
QAST::MASTOperations.add_core_moarop_mapping('abs_I', 'abs_I');
QAST::MASTOperations.add_core_moarop_mapping('abs_n', 'abs_n');
QAST::MASTOperations.add_core_moarop_mapping('ceil_n', 'ceil_n');
QAST::MASTOperations.add_core_moarop_mapping('floor_n', 'floor_n');
QAST::MASTOperations.add_core_moarop_mapping('sqrt_n', 'sqrt_n');
QAST::MASTOperations.add_core_moarop_mapping('base_I', 'base_I');
QAST::MASTOperations.add_core_moarop_mapping('isbig_I', 'isbig_I');
QAST::MASTOperations.add_core_moarop_mapping('radix', 'radix');
QAST::MASTOperations.add_core_moarop_mapping('radix_I', 'radix_I');
QAST::MASTOperations.add_core_moarop_mapping('log_n', 'log_n');
QAST::MASTOperations.add_core_moarop_mapping('exp_n', 'exp_n');
QAST::MASTOperations.add_core_moarop_mapping('isnanorinf', 'isnanorinf');
QAST::MASTOperations.add_core_moarop_mapping('inf', 'inf');
QAST::MASTOperations.add_core_moarop_mapping('neginf', 'neginf');
QAST::MASTOperations.add_core_moarop_mapping('nan', 'nan');
QAST::MASTOperations.add_core_moarop_mapping('isprime_I', 'isprime_I');
QAST::MASTOperations.add_core_moarop_mapping('rand_I', 'rand_I');

# bigint <-> string/num conversions
QAST::MASTOperations.add_core_moarop_mapping('tostr_I', 'coerce_Is');
QAST::MASTOperations.add_core_moarop_mapping('fromstr_I', 'coerce_sI');
QAST::MASTOperations.add_core_moarop_mapping('tonum_I', 'coerce_In');
QAST::MASTOperations.add_core_moarop_mapping('fromnum_I', 'coerce_nI');
QAST::MASTOperations.add_core_moarop_mapping('fromI_I', 'coerce_II');

QAST::MASTOperations.add_core_moarop_mapping('coerce_in', 'coerce_in');
QAST::MASTOperations.add_core_moarop_mapping('coerce_ni', 'coerce_ni');

QAST::MASTOperations.add_core_moarop_mapping('coerce_ui', 'coerce_ui');
QAST::MASTOperations.add_core_moarop_mapping('coerce_iu', 'coerce_iu');

QAST::MASTOperations.add_core_moarop_mapping('coerce_is', 'coerce_is');
QAST::MASTOperations.add_core_moarop_mapping('coerce_us', 'coerce_us');
QAST::MASTOperations.add_core_moarop_mapping('coerce_si', 'coerce_si');

# trig opcodes
QAST::MASTOperations.add_core_moarop_mapping('sin_n', 'sin_n');
QAST::MASTOperations.add_core_moarop_mapping('asin_n', 'asin_n');
QAST::MASTOperations.add_core_moarop_mapping('cos_n', 'cos_n');
QAST::MASTOperations.add_core_moarop_mapping('acos_n', 'acos_n');
QAST::MASTOperations.add_core_moarop_mapping('tan_n', 'tan_n');
QAST::MASTOperations.add_core_moarop_mapping('atan_n', 'atan_n');
QAST::MASTOperations.add_core_moarop_mapping('atan2_n', 'atan2_n');
QAST::MASTOperations.add_core_moarop_mapping('sec_n', 'sec_n');
QAST::MASTOperations.add_core_moarop_mapping('asec_n', 'asec_n');
QAST::MASTOperations.add_core_moarop_mapping('asin_n', 'asin_n');
QAST::MASTOperations.add_core_moarop_mapping('sinh_n', 'sinh_n');
QAST::MASTOperations.add_core_moarop_mapping('cosh_n', 'cosh_n');
QAST::MASTOperations.add_core_moarop_mapping('tanh_n', 'tanh_n');
QAST::MASTOperations.add_core_moarop_mapping('sech_n', 'sech_n');

# esoteric math opcodes
QAST::MASTOperations.add_core_moarop_mapping('gcd_i', 'gcd_i');
QAST::MASTOperations.add_core_moarop_mapping('gcd_I', 'gcd_I');
QAST::MASTOperations.add_core_moarop_mapping('lcm_i', 'lcm_i');
QAST::MASTOperations.add_core_moarop_mapping('lcm_I', 'lcm_I');

# string opcodes
QAST::MASTOperations.add_core_moarop_mapping('chars', 'chars');
QAST::MASTOperations.add_core_moarop_mapping('codes', 'codes_s');
QAST::MASTOperations.add_core_moarop_mapping('uc', 'uc');
QAST::MASTOperations.add_core_moarop_mapping('lc', 'lc');
QAST::MASTOperations.add_core_moarop_mapping('tc', 'tc');
QAST::MASTOperations.add_core_moarop_mapping('fc', 'fc');
QAST::MASTOperations.add_core_moarop_mapping('x', 'repeat_s');
QAST::MASTOperations.add_core_moarop_mapping('iscclass', 'iscclass');
QAST::MASTOperations.add_core_moarop_mapping('findcclass', 'findcclass');
QAST::MASTOperations.add_core_moarop_mapping('findnotcclass', 'findnotcclass');
QAST::MASTOperations.add_core_moarop_mapping('escape', 'escape');
QAST::MASTOperations.add_core_moarop_mapping('replace', 'replace');
QAST::MASTOperations.add_core_moarop_mapping('flip', 'flip');
QAST::MASTOperations.add_core_moarop_mapping('concat', 'concat_s');
QAST::MASTOperations.add_core_moarop_mapping('join', 'join');
QAST::MASTOperations.add_core_moarop_mapping('split', 'split');
QAST::MASTOperations.add_core_moarop_mapping('chr', 'chr');
QAST::MASTOperations.add_core_moarop_mapping('ordfirst', 'ordfirst');
QAST::MASTOperations.add_core_moarop_mapping('ordat', 'ordat');
QAST::MASTOperations.add_core_moarop_mapping('ordbaseat', 'ordbaseat');
QAST::MASTOperations.add_core_moarop_mapping('indexfrom', 'index_s');
QAST::MASTOperations.add_core_moarop_mapping('indexic', 'indexic_s');
QAST::MASTOperations.add_core_moarop_mapping('indexim', 'indexim_s');
QAST::MASTOperations.add_core_moarop_mapping('indexicim', 'indexicim_s');
QAST::MASTOperations.add_core_moarop_mapping('rindexfrom', 'rindexfrom');
QAST::MASTOperations.add_core_moarop_mapping('substr_s', 'substr_s');
QAST::MASTOperations.add_core_moarop_mapping('codepointfromname', 'getcpbyname');
QAST::MASTOperations.add_core_moarop_mapping('getcp_s', 'getcp_s');
QAST::MASTOperations.add_core_moarop_mapping('encode', 'encode');
QAST::MASTOperations.add_core_moarop_mapping('encodeconf', 'encodeconf');
QAST::MASTOperations.add_core_moarop_mapping('encoderep', 'encoderep');
QAST::MASTOperations.add_core_moarop_mapping('encoderepconf', 'encoderepconf');
QAST::MASTOperations.add_core_moarop_mapping('decode', 'decode');
QAST::MASTOperations.add_core_moarop_mapping('decodeconf', 'decodeconf');
QAST::MASTOperations.add_core_moarop_mapping('decoderepconf', 'decoderepconf');
QAST::MASTOperations.add_core_moarop_mapping('decodetocodes', 'decodetocodes', 3);
QAST::MASTOperations.add_core_moarop_mapping('encodefromcodes', 'encodefromcodes', 2);
QAST::MASTOperations.add_core_moarop_mapping('encodenorm', 'encodenorm', 3);
QAST::MASTOperations.add_core_moarop_mapping('normalizecodes', 'normalizecodes', 2);
QAST::MASTOperations.add_core_moarop_mapping('strfromcodes', 'strfromcodes');
QAST::MASTOperations.add_core_moarop_mapping('strtocodes', 'strtocodes', 2);
QAST::MASTOperations.add_core_moarop_mapping('decoderconfigure', 'decoderconfigure', 0);
QAST::MASTOperations.add_core_moarop_mapping('decodersetlineseps', 'decodersetlineseps', 0);
QAST::MASTOperations.add_core_moarop_mapping('decoderaddbytes', 'decoderaddbytes', 1);
QAST::MASTOperations.add_core_moarop_mapping('decodertakechars', 'decodertakechars');
QAST::MASTOperations.add_core_moarop_mapping('decodertakecharseof', 'decodertakecharseof');
QAST::MASTOperations.add_core_moarop_mapping('decodertakeallchars', 'decodertakeallchars');
QAST::MASTOperations.add_core_moarop_mapping('decodertakeavailablechars', 'decodertakeavailablechars');
QAST::MASTOperations.add_core_moarop_mapping('decodertakeline', 'decodertakeline');
QAST::MASTOperations.add_core_moarop_mapping('decoderbytesavailable', 'decoderbytesavailable');
QAST::MASTOperations.add_core_moarop_mapping('decodertakebytes', 'decodertakebytes');
QAST::MASTOperations.add_core_moarop_mapping('decoderempty', 'decoderempty');
QAST::MASTOperations.add_core_moarop_mapping('indexingoptimized', 'indexingoptimized');

QAST::MASTOperations.add_core_op('tclc', -> $qastcomp, $op {
    my @operands := $op.list;
    unless nqp::elems(@operands) == 1 {
        nqp::die("The 'tclc' op needs 1 argument, got " ~ nqp::elems(@operands));
    }
    $qastcomp.as_mast(
            QAST::Op.new( :op('concat'),
                QAST::Op.new( :op('tc'),
                    QAST::Op.new( :op('substr'),
                        @operands[0], QAST::IVal.new( :value(0) ), QAST::IVal.new( :value(1) ))),
                QAST::Op.new( :op('lc'),
                    QAST::Op.new( :op('substr'),
                        @operands[0], QAST::IVal.new( :value(1) ))),
        ));
});

QAST::MASTOperations.add_core_moarop_mapping('eqat', 'eqat_s');
QAST::MASTOperations.add_core_moarop_mapping('eqatic', 'eqatic_s');
QAST::MASTOperations.add_core_moarop_mapping('eqatim', 'eqatim_s');
QAST::MASTOperations.add_core_moarop_mapping('eqaticim', 'eqaticim_s');


QAST::MASTOperations.add_core_op('substr', -> $qastcomp, $op {
    my @operands := $op.list;
    if nqp::elems(@operands) == 2 { nqp::push(@operands, QAST::IVal.new( :value(-1) )) }
    $qastcomp.as_mast(QAST::Op.new( :op('substr_s'), |@operands ));
});

QAST::MASTOperations.add_core_op('ord',  -> $qastcomp, $op {
    my @operands := $op.list;
    $qastcomp.as_mast(nqp::elems(@operands) == 1
        ?? QAST::Op.new( :op('ordfirst'), |@operands )
        !! QAST::Op.new( :op('ordat'), |@operands ));
});

QAST::MASTOperations.add_core_op('index',  -> $qastcomp, $op {
    my @operands := $op.list;
    $qastcomp.as_mast(nqp::elems(@operands) == 2
        ?? QAST::Op.new( :op('indexfrom'), |@operands, QAST::IVal.new( :value(0)) )
        !! QAST::Op.new( :op('indexfrom'), |@operands ));
});

QAST::MASTOperations.add_core_op('rindex',  -> $qastcomp, $op {
    my @operands := $op.list;
    $qastcomp.as_mast(nqp::elems(@operands) == 2
        ?? QAST::Op.new( :op('rindexfrom'), |@operands, QAST::IVal.new( :value(-1) ) )
        !! QAST::Op.new( :op('rindexfrom'), |@operands ));
});

# unicode properties
QAST::MASTOperations.add_core_moarop_mapping('unipropcode', 'unipropcode');
QAST::MASTOperations.add_core_moarop_mapping('unipvalcode', 'unipvalcode');
QAST::MASTOperations.add_core_moarop_mapping('hasuniprop', 'hasuniprop');
QAST::MASTOperations.add_core_moarop_mapping('getuniname', 'getuniname');
QAST::MASTOperations.add_core_moarop_mapping('getuniprop_str', 'getuniprop_str');
QAST::MASTOperations.add_core_moarop_mapping('getuniprop_bool', 'getuniprop_bool');
QAST::MASTOperations.add_core_moarop_mapping('getuniprop_int', 'getuniprop_int');
QAST::MASTOperations.add_core_moarop_mapping('matchuniprop', 'matchuniprop');

# serialization context opcodes
QAST::MASTOperations.add_core_moarop_mapping('sha1', 'sha1');
QAST::MASTOperations.add_core_moarop_mapping('createsc', 'createsc');
QAST::MASTOperations.add_core_moarop_mapping('scsetobj', 'scsetobj', 2);
QAST::MASTOperations.add_core_moarop_mapping('scsetcode', 'scsetcode', 2);
QAST::MASTOperations.add_core_moarop_mapping('scgetobj', 'scgetobj');
QAST::MASTOperations.add_core_moarop_mapping('scgethandle', 'scgethandle');
QAST::MASTOperations.add_core_moarop_mapping('scgetdesc', 'scgetdesc');
QAST::MASTOperations.add_core_moarop_mapping('scgetobjidx', 'scgetobjidx');
QAST::MASTOperations.add_core_moarop_mapping('scsetdesc', 'scsetdesc', 1);
QAST::MASTOperations.add_core_moarop_mapping('scobjcount', 'scobjcount');
QAST::MASTOperations.add_core_moarop_mapping('setobjsc', 'setobjsc', 0);
QAST::MASTOperations.add_core_moarop_mapping('getobjsc', 'getobjsc');
QAST::MASTOperations.add_core_moarop_mapping('serialize', 'serialize');
QAST::MASTOperations.add_core_moarop_mapping('deserialize', 'deserialize', 0);
QAST::MASTOperations.add_core_moarop_mapping('scwbdisable', 'scwbdisable');
QAST::MASTOperations.add_core_moarop_mapping('scwbenable', 'scwbenable');
QAST::MASTOperations.add_core_moarop_mapping('pushcompsc', 'pushcompsc', 0);
QAST::MASTOperations.add_core_moarop_mapping('popcompsc', 'popcompsc');
QAST::MASTOperations.add_core_moarop_mapping('neverrepossess', 'neverrepossess', 0);
QAST::MASTOperations.add_core_moarop_mapping('scdisclaim', 'scdisclaim', 0);

# bitwise opcodes
QAST::MASTOperations.add_core_moarop_mapping('bitor_i', 'bor_i');
QAST::MASTOperations.add_core_moarop_mapping('bitxor_i', 'bxor_i');
QAST::MASTOperations.add_core_moarop_mapping('bitand_i', 'band_i');
QAST::MASTOperations.add_core_moarop_mapping('bitshiftl_i', 'blshift_i');
QAST::MASTOperations.add_core_moarop_mapping('bitshiftr_i', 'brshift_i');
QAST::MASTOperations.add_core_moarop_mapping('bitneg_i', 'bnot_i');

QAST::MASTOperations.add_core_moarop_mapping('bitor_I', 'bor_I');
QAST::MASTOperations.add_core_moarop_mapping('bitxor_I', 'bxor_I');
QAST::MASTOperations.add_core_moarop_mapping('bitand_I', 'band_I');
QAST::MASTOperations.add_core_moarop_mapping('bitneg_I', 'bnot_I');
QAST::MASTOperations.add_core_moarop_mapping('bitshiftl_I', 'blshift_I');
QAST::MASTOperations.add_core_moarop_mapping('bitshiftr_I', 'brshift_I');

# string bitwise ops
QAST::MASTOperations.add_core_moarop_mapping('bitor_s', 'bitor_s');
QAST::MASTOperations.add_core_moarop_mapping('bitxor_s', 'bitxor_s');
QAST::MASTOperations.add_core_moarop_mapping('bitand_s', 'bitand_s');

# relational opcodes
QAST::MASTOperations.add_core_moarop_mapping('cmp_i', 'cmp_i');
QAST::MASTOperations.add_core_moarop_mapping('iseq_i', 'eq_i');
QAST::MASTOperations.add_core_moarop_mapping('isne_i', 'ne_i');
QAST::MASTOperations.add_core_moarop_mapping('islt_i', 'lt_i');
QAST::MASTOperations.add_core_moarop_mapping('isle_i', 'le_i');
QAST::MASTOperations.add_core_moarop_mapping('isgt_i', 'gt_i');
QAST::MASTOperations.add_core_moarop_mapping('isge_i', 'ge_i');

QAST::MASTOperations.add_core_moarop_mapping('cmp_n', 'cmp_n');
QAST::MASTOperations.add_core_moarop_mapping('not_i', 'not_i');
QAST::MASTOperations.add_core_moarop_mapping('iseq_n', 'eq_n');
QAST::MASTOperations.add_core_moarop_mapping('isne_n', 'ne_n');
QAST::MASTOperations.add_core_moarop_mapping('islt_n', 'lt_n');
QAST::MASTOperations.add_core_moarop_mapping('isle_n', 'le_n');
QAST::MASTOperations.add_core_moarop_mapping('isgt_n', 'gt_n');
QAST::MASTOperations.add_core_moarop_mapping('isge_n', 'ge_n');

QAST::MASTOperations.add_core_moarop_mapping('cmp_s', 'cmp_s');
QAST::MASTOperations.add_core_moarop_mapping('unicmp_s', 'unicmp_s');
QAST::MASTOperations.add_core_moarop_mapping('strfromname', 'strfromname');
QAST::MASTOperations.add_core_moarop_mapping('iseq_s', 'eq_s');
QAST::MASTOperations.add_core_moarop_mapping('isne_s', 'ne_s');
QAST::MASTOperations.add_core_moarop_mapping('islt_s', 'lt_s');
QAST::MASTOperations.add_core_moarop_mapping('isle_s', 'le_s');
QAST::MASTOperations.add_core_moarop_mapping('isgt_s', 'gt_s');
QAST::MASTOperations.add_core_moarop_mapping('isge_s', 'ge_s');

QAST::MASTOperations.add_core_moarop_mapping('bool_I', 'bool_I');
QAST::MASTOperations.add_core_moarop_mapping('cmp_I', 'cmp_I');
QAST::MASTOperations.add_core_moarop_mapping('iseq_I', 'eq_I');
QAST::MASTOperations.add_core_moarop_mapping('isne_I', 'ne_I');
QAST::MASTOperations.add_core_moarop_mapping('islt_I', 'lt_I');
QAST::MASTOperations.add_core_moarop_mapping('isle_I', 'le_I');
QAST::MASTOperations.add_core_moarop_mapping('isgt_I', 'gt_I');
QAST::MASTOperations.add_core_moarop_mapping('isge_I', 'ge_I');

# aggregate opcodes
QAST::MASTOperations.add_core_moarop_mapping('atpos', 'atpos_o');
QAST::MASTOperations.add_core_moarop_mapping('atpos_i', 'atpos_i');
QAST::MASTOperations.add_core_moarop_mapping('atpos_n', 'atpos_n');
QAST::MASTOperations.add_core_moarop_mapping('atpos_s', 'atpos_s');
QAST::MASTOperations.add_core_moarop_mapping('atposref_i', 'atposref_i');
QAST::MASTOperations.add_core_moarop_mapping('atposref_n', 'atposref_n');
QAST::MASTOperations.add_core_moarop_mapping('atposref_s', 'atposref_s');
QAST::MASTOperations.add_core_moarop_mapping('atpos2d', 'atpos2d_o');
QAST::MASTOperations.add_core_moarop_mapping('atpos2d_i', 'atpos2d_i');
QAST::MASTOperations.add_core_moarop_mapping('atpos2d_n', 'atpos2d_n');
QAST::MASTOperations.add_core_moarop_mapping('atpos2d_s', 'atpos2d_s');
QAST::MASTOperations.add_core_moarop_mapping('atpos3d', 'atpos3d_o');
QAST::MASTOperations.add_core_moarop_mapping('atpos3d_i', 'atpos3d_i');
QAST::MASTOperations.add_core_moarop_mapping('atpos3d_n', 'atpos3d_n');
QAST::MASTOperations.add_core_moarop_mapping('atpos3d_s', 'atpos3d_s');
QAST::MASTOperations.add_core_moarop_mapping('atposnd', 'atposnd_o');
QAST::MASTOperations.add_core_moarop_mapping('atposnd_i', 'atposnd_i');
QAST::MASTOperations.add_core_moarop_mapping('atposnd_n', 'atposnd_n');
QAST::MASTOperations.add_core_moarop_mapping('atposnd_s', 'atposnd_s');
QAST::MASTOperations.add_core_moarop_mapping('multidimref_i', 'multidimref_i');
QAST::MASTOperations.add_core_moarop_mapping('multidimref_n', 'multidimref_n');
QAST::MASTOperations.add_core_moarop_mapping('multidimref_s', 'multidimref_s');
QAST::MASTOperations.add_core_moarop_mapping('atkey', 'atkey_o');
QAST::MASTOperations.add_core_moarop_mapping('atkey_i', 'atkey_i');
QAST::MASTOperations.add_core_moarop_mapping('atkey_u', 'atkey_u');
QAST::MASTOperations.add_core_moarop_mapping('atkey_n', 'atkey_n');
QAST::MASTOperations.add_core_moarop_mapping('atkey_s', 'atkey_s');
QAST::MASTOperations.add_core_moarop_mapping('bindpos', 'bindpos_o', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindpos_i', 'bindpos_i', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindpos_n', 'bindpos_n', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindpos_s', 'bindpos_s', 2);

QAST::MASTOperations.add_core_moarop_mapping('bindpos2d', 'bindpos2d_o', 3);
QAST::MASTOperations.add_core_moarop_mapping('bindpos2d_i', 'bindpos2d_i', 3);
QAST::MASTOperations.add_core_moarop_mapping('bindpos2d_n', 'bindpos2d_n', 3);
QAST::MASTOperations.add_core_moarop_mapping('bindpos2d_s', 'bindpos2d_s', 3);
QAST::MASTOperations.add_core_moarop_mapping('bindpos3d', 'bindpos3d_o', 4);
QAST::MASTOperations.add_core_moarop_mapping('bindpos3d_i', 'bindpos3d_i', 4);
QAST::MASTOperations.add_core_moarop_mapping('bindpos3d_n', 'bindpos3d_n', 4);
QAST::MASTOperations.add_core_moarop_mapping('bindpos3d_s', 'bindpos3d_s', 4);
QAST::MASTOperations.add_core_moarop_mapping('bindposnd', 'bindposnd_o', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindposnd_i', 'bindposnd_i', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindposnd_n', 'bindposnd_n', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindposnd_s', 'bindposnd_s', 2);
QAST::MASTOperations.add_core_moarop_mapping('writeint', 'writeint');
QAST::MASTOperations.add_core_moarop_mapping('writeuint', 'writeuint');
QAST::MASTOperations.add_core_moarop_mapping('writenum', 'writenum');
QAST::MASTOperations.add_core_moarop_mapping('readint', 'readint');
QAST::MASTOperations.add_core_moarop_mapping('readuint', 'readuint');
QAST::MASTOperations.add_core_moarop_mapping('readnum', 'readnum');
QAST::MASTOperations.add_core_moarop_mapping('bindkey', 'bindkey_o', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindkey_i', 'bindkey_i', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindkey_n', 'bindkey_n', 2);
QAST::MASTOperations.add_core_moarop_mapping('bindkey_s', 'bindkey_s', 2);
QAST::MASTOperations.add_core_moarop_mapping('existskey', 'existskey');
QAST::MASTOperations.add_core_moarop_mapping('deletekey', 'deletekey');
QAST::MASTOperations.add_core_moarop_mapping('elems', 'elems');
QAST::MASTOperations.add_core_moarop_mapping('setelems', 'setelemspos', 0);
QAST::MASTOperations.add_core_moarop_mapping('dimensions', 'dimensions');
QAST::MASTOperations.add_core_moarop_mapping('setdimensions', 'setdimensions', 0);
QAST::MASTOperations.add_core_moarop_mapping('numdimensions', 'numdimensions');
QAST::MASTOperations.add_core_moarop_mapping('existspos', 'existspos');
QAST::MASTOperations.add_core_moarop_mapping('push', 'push_o', 1);
QAST::MASTOperations.add_core_moarop_mapping('push_i', 'push_i', 1);
QAST::MASTOperations.add_core_moarop_mapping('push_n', 'push_n', 1);
QAST::MASTOperations.add_core_moarop_mapping('push_s', 'push_s', 1);
QAST::MASTOperations.add_core_moarop_mapping('pop', 'pop_o');
QAST::MASTOperations.add_core_moarop_mapping('pop_i', 'pop_i');
QAST::MASTOperations.add_core_moarop_mapping('pop_n', 'pop_n');
QAST::MASTOperations.add_core_moarop_mapping('pop_s', 'pop_s');
QAST::MASTOperations.add_core_moarop_mapping('unshift', 'unshift_o', 1);
QAST::MASTOperations.add_core_moarop_mapping('unshift_i', 'unshift_i', 1);
QAST::MASTOperations.add_core_moarop_mapping('unshift_n', 'unshift_n', 1);
QAST::MASTOperations.add_core_moarop_mapping('unshift_s', 'unshift_s', 1);
QAST::MASTOperations.add_core_moarop_mapping('shift', 'shift_o');
QAST::MASTOperations.add_core_moarop_mapping('shift_i', 'shift_i');
QAST::MASTOperations.add_core_moarop_mapping('shift_n', 'shift_n');
QAST::MASTOperations.add_core_moarop_mapping('shift_s', 'shift_s');
QAST::MASTOperations.add_core_moarop_mapping('splice', 'splice', 0);
QAST::MASTOperations.add_core_moarop_mapping('slice', 'slice');
QAST::MASTOperations.add_core_moarop_mapping('isint', 'isint', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('isnum', 'isnum', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('isstr', 'isstr', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('islist', 'islist', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('ishash', 'ishash', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('iterator', 'iter');
QAST::MASTOperations.add_core_moarop_mapping('iterkey_s', 'iterkey_s');
QAST::MASTOperations.add_core_moarop_mapping('iterval', 'iterval');

# object opcodes
QAST::MASTOperations.add_core_op('null', -> $qastcomp, $op {
    my $want := $*WANT;
    if nqp::isconcrete($want) && $want == $MVM_reg_void {
        MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
    }
    else {
        my $res_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
        op_null($res_reg);
        MAST::InstructionList.new($res_reg, $MVM_reg_obj)
    }
});
QAST::MASTOperations.add_core_moarop_mapping('null_s', 'null_s');
QAST::MASTOperations.add_core_moarop_mapping('what', 'getwhat', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('how', 'gethow', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('who', 'getwho', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('where', 'getwhere', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('objectid', 'objectid', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('findmethod', 'findmeth_s', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('tryfindmethod', 'tryfindmeth_s', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('setwho', 'setwho', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('rebless', 'rebless', :decont(0, 1));
QAST::MASTOperations.add_core_moarop_mapping('knowhow', 'knowhow');
QAST::MASTOperations.add_core_moarop_mapping('knowhowattr', 'knowhowattr');
QAST::MASTOperations.add_core_moarop_mapping('bootint', 'bootint');
QAST::MASTOperations.add_core_moarop_mapping('bootnum', 'bootnum');
QAST::MASTOperations.add_core_moarop_mapping('bootstr', 'bootstr');
QAST::MASTOperations.add_core_moarop_mapping('bootarray', 'bootarray');
QAST::MASTOperations.add_core_moarop_mapping('bootintarray', 'bootintarray');
QAST::MASTOperations.add_core_moarop_mapping('bootnumarray', 'bootnumarray');
QAST::MASTOperations.add_core_moarop_mapping('bootstrarray', 'bootstrarray');
QAST::MASTOperations.add_core_moarop_mapping('boothash', 'boothash');
QAST::MASTOperations.add_core_moarop_mapping('hlllist', 'hlllist');
QAST::MASTOperations.add_core_moarop_mapping('hllhash', 'hllhash');
QAST::MASTOperations.add_core_moarop_mapping('create', 'create');
QAST::MASTOperations.add_core_moarop_mapping('clone', 'clone', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('isconcrete', 'isconcrete', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('iscont', 'iscont');
QAST::MASTOperations.add_core_moarop_mapping('iscont_i', 'iscont_i');
QAST::MASTOperations.add_core_moarop_mapping('iscont_n', 'iscont_n');
QAST::MASTOperations.add_core_moarop_mapping('iscont_s', 'iscont_s');
QAST::MASTOperations.add_core_moarop_mapping('isrwcont', 'isrwcont');
QAST::MASTOperations.add_core_op('decont', -> $qastcomp, $op {
    if nqp::elems($op.list) != 1 {
        nqp::die("The 'decont' op needs 1 operand, got " ~ nqp::elems($op.list));
    }
    my $regalloc := $*REGALLOC;
    my $res_reg := $regalloc.fresh_o();
    my $expr := $qastcomp.as_mast($op[0], :want($MVM_reg_obj), :want-decont);
    op_decont($res_reg, $expr.result_reg);
    $regalloc.release_register($expr.result_reg, $MVM_reg_obj);
    MAST::InstructionList.new($res_reg, $MVM_reg_obj)
});
QAST::MASTOperations.add_core_moarop_mapping('decont', 'decont');
QAST::MASTOperations.add_core_op('wantdecont', -> $qastcomp, $op {
    $qastcomp.as_mast($op[0], :want-decont)
});
QAST::MASTOperations.add_core_moarop_mapping('decont_i', 'decont_i');
QAST::MASTOperations.add_core_moarop_mapping('decont_n', 'decont_n');
QAST::MASTOperations.add_core_moarop_mapping('decont_s', 'decont_s');
QAST::MASTOperations.add_core_moarop_mapping('isnull', 'isnull');
QAST::MASTOperations.add_core_moarop_mapping('isnull_s', 'isnull_s');
QAST::MASTOperations.add_core_moarop_mapping('istrue', 'istrue', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('isfalse', 'isfalse', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('istype', 'istype', :decont(0, 1));
QAST::MASTOperations.add_core_moarop_mapping('eqaddr', 'eqaddr');
QAST::MASTOperations.add_core_moarop_mapping('attrinited', 'attrinited', :decont(1));

sub add_bindattr_op($nqpop, $hintedop, $namedop, $want) {
    QAST::MASTOperations.add_core_op($nqpop, -> $qastcomp, $op {
        my $regalloc := $*REGALLOC;
        my $val_mast := $qastcomp.as_mast( :$want, $op[3] );
        my $obj_mast := $qastcomp.as_mast( :want($MVM_reg_obj), $op[0] );
        my $type_mast := $qastcomp.as_mast( :want($MVM_reg_obj),
            nqp::istype($op[1], QAST::WVal) && !nqp::isconcrete($op[1].value)
                ?? $op[1]
                !! QAST::Op.new( :op('decont'), $op[1] ));
        my int $hint := -1;
        my $name := $op[2];
        $name := $name[2] if nqp::istype($name, QAST::Want) && $name[1] eq 'Ss';
        if nqp::istype($name, QAST::SVal) {
            if nqp::istype($op[1], QAST::WVal) {
                $hint := nqp::hintfor($op[1].value, $name.value);
            }
            %core_op_generators{$hintedop}($obj_mast.result_reg, $type_mast.result_reg,
                $name.value, $val_mast.result_reg, $hint);
        } else {
            my $name_mast := $qastcomp.as_mast( :want($MVM_reg_str), $op[2] );
            %core_op_generators{$namedop}($obj_mast.result_reg, $type_mast.result_reg,
                $name_mast.result_reg, $val_mast.result_reg);
            $regalloc.release_register($name_mast.result_reg, $MVM_reg_str);
        }
        $regalloc.release_register($obj_mast.result_reg, $MVM_reg_obj);
        $regalloc.release_register($type_mast.result_reg, $MVM_reg_obj);
        MAST::InstructionList.new($val_mast.result_reg, $want)
    })
}

add_bindattr_op('bindattr',   'bindattr_o', 'bindattrs_o', $MVM_reg_obj);
add_bindattr_op('bindattr_i', 'bindattr_i', 'bindattrs_i', $MVM_reg_int64);
add_bindattr_op('bindattr_n', 'bindattr_n', 'bindattrs_n', $MVM_reg_num64);
add_bindattr_op('bindattr_s', 'bindattr_s', 'bindattrs_s', $MVM_reg_str);

sub add_getattr_op($nqpop, $hintedop, $namedop, $want) {
    QAST::MASTOperations.add_core_op($nqpop, -> $qastcomp, $op {
        my $regalloc := $*REGALLOC;
        my $obj_mast := $qastcomp.as_mast( :want($MVM_reg_obj), $op[0] );
        my $type_mast := $qastcomp.as_mast( :want($MVM_reg_obj),
            nqp::istype($op[1], QAST::WVal) && !nqp::isconcrete($op[1].value)
                ?? $op[1]
                !! QAST::Op.new( :op('decont'), $op[1] ));
        my int $hint := -1;
        my $res_reg := $regalloc.fresh_register($want);
        my $name := $op[2];
        $name := $name[2] if nqp::istype($name, QAST::Want) && $name[1] eq 'Ss';
        if nqp::istype($name, QAST::SVal) {
            if nqp::istype($op[1], QAST::WVal) {
                $hint := nqp::hintfor($op[1].value, $name.value);
            }
            %core_op_generators{$hintedop}($res_reg, $obj_mast.result_reg, $type_mast.result_reg,
                $name.value, $hint);
        } else {
            my $name_mast := $qastcomp.as_mast( :want($MVM_reg_str), $op[2] );
            %core_op_generators{$namedop}($res_reg, $obj_mast.result_reg, $type_mast.result_reg,
                $name_mast.result_reg);
            $regalloc.release_register($name_mast.result_reg, $MVM_reg_str);
        }
        $regalloc.release_register($obj_mast.result_reg, $MVM_reg_obj);
        $regalloc.release_register($type_mast.result_reg, $MVM_reg_obj);
        MAST::InstructionList.new($res_reg, $want)
    })
}

add_getattr_op('getattr',   'getattr_o', 'getattrs_o', $MVM_reg_obj);
add_getattr_op('getattr_i', 'getattr_i', 'getattrs_i', $MVM_reg_int64);
add_getattr_op('getattr_n', 'getattr_n', 'getattrs_n', $MVM_reg_num64);
add_getattr_op('getattr_s', 'getattr_s', 'getattrs_s', $MVM_reg_str);

add_getattr_op('getattrref_i', 'getattrref_i', 'getattrsref_i', $MVM_reg_obj);
add_getattr_op('getattrref_n', 'getattrref_n', 'getattrsref_n', $MVM_reg_obj);
add_getattr_op('getattrref_s', 'getattrref_s', 'getattrsref_s', $MVM_reg_obj);

QAST::MASTOperations.add_core_moarop_mapping('hintfor', 'hintfor');
QAST::MASTOperations.add_core_moarop_mapping('unbox_i', 'unbox_i', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('unbox_n', 'unbox_n', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('unbox_s', 'unbox_s', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('unbox_u', 'unbox_u', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('box_i', 'box_i');
QAST::MASTOperations.add_core_moarop_mapping('box_n', 'box_n');
QAST::MASTOperations.add_core_moarop_mapping('box_s', 'box_s');
QAST::MASTOperations.add_core_moarop_mapping('box_u', 'box_u');
QAST::MASTOperations.add_core_moarop_mapping('hllboxtype_i', 'hllboxtype_i');
QAST::MASTOperations.add_core_moarop_mapping('hllboxtype_n', 'hllboxtype_n');
QAST::MASTOperations.add_core_moarop_mapping('hllboxtype_s', 'hllboxtype_s');
QAST::MASTOperations.add_core_moarop_mapping('can', 'can_s', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('reprname', 'reprname', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('newtype', 'newtype', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('newmixintype', 'newmixintype', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('composetype', 'composetype');
QAST::MASTOperations.add_core_moarop_mapping('setboolspec', 'setboolspec', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('setmethcache', 'setmethcache', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('setmethcacheauth', 'setmethcacheauth', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('settypecache', 'settypecache', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('settypecheckmode', 'settypecheckmode', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('settypefinalize', 'settypefinalize', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('isinvokable', 'isinvokable');
QAST::MASTOperations.add_core_moarop_mapping('setinvokespec', 'setinvokespec', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('setmultispec', 'setmultispec', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('setcontspec', 'setcontspec', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('assign', 'assign', 0, :decont(1));

sub try_get_bind_scope($var) {
    if nqp::istype($var, QAST::Var) {
        my str $scope := $var.scope;
        if $scope eq 'attributeref' {
            return 'attribute';
        }
        elsif $scope eq 'lexicalref' {
            # Make sure we've got the lexical itself in scope to bind to.
            my $lex;
            my $lexref;
            my $outer := 0;
            my $block := $*BLOCK;
            my $name  := $var.name;
            while nqp::istype($block, BlockInfo) {
                last if $block.qast.ann('DYN_COMP_WRAPPER');
                $lex := $block.lexical($name);
                last if $lex;
                last if $block.lexicalref($name);
                $block := $block.outer;
                $outer++;
            }
            if $lex {
                return 'lexical';
            }
        }
    }
    ''
}
sub add_native_assign_op($op_name, $kind) {
    QAST::MASTOperations.add_core_op($op_name, -> $qastcomp, $op {
        my @operands := $op.list;
        unless nqp::elems(@operands) == 2 {
            nqp::die("The '$op' op needs 2 arguments, got " ~ nqp::elems(@operands));
        }
        my $target := @operands[0];
        if try_get_bind_scope($target) -> $bind_scope {
            # Can lower it to a bind instead.
            $op.op('bind');
            $target.scope($bind_scope);
            $qastcomp.as_mast($op)
        }
        else {
            # Really need to emit an assign.
            my $regalloc := $*REGALLOC;
            my $target_mast := $qastcomp.as_mast( :want($MVM_reg_obj), $op[0] );
            my $value_mast  := $qastcomp.as_mast( :want($kind), $op[1] );
            %core_op_generators{$op_name}($target_mast.result_reg, $value_mast.result_reg);
            $regalloc.release_register($value_mast.result_reg, $kind);
            MAST::InstructionList.new($target_mast.result_reg, $MVM_reg_obj)
        }
    })
}
add_native_assign_op('assign_i', $MVM_reg_int64);
add_native_assign_op('assign_n', $MVM_reg_num64);
add_native_assign_op('assign_s', $MVM_reg_str);

QAST::MASTOperations.add_core_moarop_mapping('assignunchecked', 'assignunchecked', 0, :decont(1));
QAST::MASTOperations.add_core_moarop_mapping('setparameterizer', 'setparameterizer', 0, :decont(0, 1));
QAST::MASTOperations.add_core_moarop_mapping('parameterizetype', 'parameterizetype', :decont(0, 1));
QAST::MASTOperations.add_core_moarop_mapping('typeparameterized', 'typeparameterized', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('typeparameters', 'typeparameters', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('typeparameterat', 'typeparameterat', :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('setdebugtypename', 'setdebugtypename', 0);

# object ops that don't do the usual decontainerization
QAST::MASTOperations.add_core_moarop_mapping('what_nd', 'getwhat');
QAST::MASTOperations.add_core_moarop_mapping('isconcrete_nd', 'isconcrete');
QAST::MASTOperations.add_core_moarop_mapping('clone_nd', 'clone');
QAST::MASTOperations.add_core_moarop_mapping('how_nd', 'gethow');
QAST::MASTOperations.add_core_moarop_mapping('istype_nd', 'istype');

# defined - overridden by HLL, but by default same as .DEFINITE.
QAST::MASTOperations.add_core_moarop_mapping('defined', 'isconcrete', :decont(0));

# lexical related opcodes
QAST::MASTOperations.add_core_moarop_mapping('getlex', 'getlex_no');
QAST::MASTOperations.add_core_moarop_mapping('getlex_i', 'getlex_ni');
QAST::MASTOperations.add_core_moarop_mapping('getlex_n', 'getlex_nn');
QAST::MASTOperations.add_core_moarop_mapping('getlex_s', 'getlex_ns');
QAST::MASTOperations.add_core_moarop_mapping('getlexref_i', 'getlexref_ni');
QAST::MASTOperations.add_core_moarop_mapping('getlexref_n', 'getlexref_nn');
QAST::MASTOperations.add_core_moarop_mapping('getlexref_s', 'getlexref_ns');
QAST::MASTOperations.add_core_moarop_mapping('bindlex', 'bindlex_no', 1);
QAST::MASTOperations.add_core_moarop_mapping('bindlex_i', 'bindlex_ni', 1);
QAST::MASTOperations.add_core_moarop_mapping('bindlex_n', 'bindlex_nn', 1);
QAST::MASTOperations.add_core_moarop_mapping('bindlex_s', 'bindlex_ns', 1);
QAST::MASTOperations.add_core_moarop_mapping('getlexdyn', 'getdynlex');
QAST::MASTOperations.add_core_moarop_mapping('bindlexdyn', 'binddynlex');
QAST::MASTOperations.add_core_moarop_mapping('getlexouter', 'getlexouter');
QAST::MASTOperations.add_core_moarop_mapping('getlexrel', 'getlexrel');
QAST::MASTOperations.add_core_moarop_mapping('getlexreldyn', 'getlexreldyn');
QAST::MASTOperations.add_core_moarop_mapping('getlexrelcaller', 'getlexrelcaller');
QAST::MASTOperations.add_core_moarop_mapping('getlexcaller', 'getlexcaller');
QAST::MASTOperations.add_core_op('locallifetime', -> $qastcomp, $op {
    # TODO: take advantage of this info for code-gen, if possible.
    $qastcomp.as_mast($op[0], :want($*WANT))
});

# code object related opcodes
# XXX explicit takeclosure will go away under new model; for now, no-op it.
QAST::MASTOperations.add_core_op('takeclosure', -> $qastcomp, $op {
    unless nqp::elems($op) == 1 {
        nqp::die("The 'takeclosure' op needs 1 argument, got "
            ~ nqp::elems($op));
    }
    $qastcomp.as_mast($op[0])
});
QAST::MASTOperations.add_core_moarop_mapping('getcodeobj', 'getcodeobj');
QAST::MASTOperations.add_core_moarop_mapping('setcodeobj', 'setcodeobj', 0);
QAST::MASTOperations.add_core_moarop_mapping('getcodename', 'getcodename');
QAST::MASTOperations.add_core_moarop_mapping('setcodename', 'setcodename', 0);
QAST::MASTOperations.add_core_moarop_mapping('forceouterctx', 'forceouterctx', 0);
QAST::MASTOperations.add_core_moarop_mapping('setdispatcher', 'setdispatcher', 0);
QAST::MASTOperations.add_core_moarop_mapping('setdispatcherfor', 'setdispatcherfor', 0);
QAST::MASTOperations.add_core_moarop_mapping('nextdispatcherfor', 'nextdispatcherfor', 0);
QAST::MASTOperations.add_core_op('takedispatcher', -> $qastcomp, $op {
    my $regalloc := $*REGALLOC;
    unless nqp::istype($op[0], QAST::SVal) {
        nqp::die("The 'takedispatcher' op must have a single QAST::SVal child, got " ~ $op[0].HOW.name($op[0]));
    }
    my $disp_reg   := $regalloc.fresh_register($MVM_reg_obj);
    my $isnull_reg := $regalloc.fresh_register($MVM_reg_int64);
    my $done_lbl   := MAST::Label.new();
    %core_op_generators{'takedispatcher'}($disp_reg);
    %core_op_generators{'isnull'}($isnull_reg, $disp_reg);
    %core_op_generators{'if_i'}($isnull_reg, $done_lbl);
    if $*BLOCK.lexical($op[0].value) -> $lex {
        %core_op_generators{'bindlex'}($lex, $disp_reg);
    }
    $*MAST_FRAME.add-label($done_lbl);
    $regalloc.release_register($disp_reg, $MVM_reg_obj);
    $regalloc.release_register($isnull_reg, $MVM_reg_int64);
    MAST::InstructionList.new(MAST::VOID, $MVM_reg_void)
});
QAST::MASTOperations.add_core_op('takenextdispatcher', -> $qastcomp, $op {
    my $regalloc := $*REGALLOC;
    unless nqp::istype($op[0], QAST::SVal) {
        nqp::die("The 'takenextdispatcher' op must have a single QAST::SVal child, got " ~ $op[0].HOW.name($op[0]));
    }
    my $disp_reg   := $regalloc.fresh_register($MVM_reg_obj);
    my $isnull_reg := $regalloc.fresh_register($MVM_reg_int64);
    my $done_lbl   := MAST::Label.new();
    %core_op_generators{'takenextdispatcher'}($disp_reg);
    %core_op_generators{'isnull'}($isnull_reg, $disp_reg);
    %core_op_generators{'if_i'}($isnull_reg, $done_lbl);
    if $*BLOCK.lexical($op[0].value) -> $lex {
        %core_op_generators{'bindlex'}($lex, $disp_reg);
    }
    $*MAST_FRAME.add-label($done_lbl);
    $regalloc.release_register($disp_reg, $MVM_reg_obj);
    $regalloc.release_register($isnull_reg, $MVM_reg_int64);
    MAST::InstructionList.new(MAST::VOID, $MVM_reg_void)
});
QAST::MASTOperations.add_core_moarop_mapping('cleardispatcher', 'takedispatcher');
QAST::MASTOperations.add_core_moarop_mapping('clearnextdispatcher', 'takenextdispatcher');
QAST::MASTOperations.add_core_moarop_mapping('freshcoderef', 'freshcoderef');
QAST::MASTOperations.add_core_moarop_mapping('iscoderef', 'iscoderef');
QAST::MASTOperations.add_core_moarop_mapping('markcodestatic', 'markcodestatic');
QAST::MASTOperations.add_core_moarop_mapping('markcodestub', 'markcodestub');
QAST::MASTOperations.add_core_moarop_mapping('getstaticcode', 'getstaticcode');
QAST::MASTOperations.add_core_moarop_mapping('getcodecuid', 'getcodecuid');
QAST::MASTOperations.add_core_moarop_mapping('captureinnerlex', 'captureinnerlex', 0);

# language/compiler ops
QAST::MASTOperations.add_core_moarop_mapping('getcomp', 'getcomp');
QAST::MASTOperations.add_core_moarop_mapping('bindcomp', 'bindcomp');
QAST::MASTOperations.add_core_moarop_mapping('gethllsym', 'gethllsym');
QAST::MASTOperations.add_core_moarop_mapping('bindhllsym', 'bindhllsym', 2);
QAST::MASTOperations.add_core_moarop_mapping('getcurhllsym', 'getcurhllsym');
QAST::MASTOperations.add_core_moarop_mapping('bindcurhllsym', 'bindcurhllsym');
QAST::MASTOperations.add_core_moarop_mapping('sethllconfig', 'sethllconfig');
QAST::MASTOperations.add_core_moarop_mapping('loadbytecode', 'loadbytecode');
QAST::MASTOperations.add_core_moarop_mapping('loadbytecodebuffer', 'loadbytecodebuffer');
QAST::MASTOperations.add_core_moarop_mapping('buffertocu', 'buffertocu');
QAST::MASTOperations.add_core_moarop_mapping('loadbytecodefh', 'loadbytecodefh');
QAST::MASTOperations.add_core_moarop_mapping('settypehll', 'settypehll', 0);
QAST::MASTOperations.add_core_moarop_mapping('settypehllrole', 'settypehllrole', 0);
QAST::MASTOperations.add_core_moarop_mapping('usecompileehllconfig', 'usecompileehllconfig');
QAST::MASTOperations.add_core_moarop_mapping('usecompilerhllconfig', 'usecompilerhllconfig');
QAST::MASTOperations.add_core_moarop_mapping('hllize', 'hllize');
QAST::MASTOperations.add_core_moarop_mapping('hllizefor', 'hllizefor');

# regex engine related opcodes
QAST::MASTOperations.add_core_moarop_mapping('nfafromstatelist', 'nfafromstatelist');
QAST::MASTOperations.add_core_moarop_mapping('nfarunproto', 'nfarunproto');
QAST::MASTOperations.add_core_moarop_mapping('nfarunalt', 'nfarunalt', 0);

# native call ops
QAST::MASTOperations.add_core_moarop_mapping('initnativecall', 'no_op');
QAST::MASTOperations.add_core_moarop_mapping('buildnativecall', 'nativecallbuild');
QAST::MASTOperations.add_core_moarop_mapping('nativecallinvoke', 'nativecallinvoke');
QAST::MASTOperations.add_core_op('nativecall', -> $qastcomp, $op {
    proto decont_all(@args) {
        my int $i := 0;
        my int $n := nqp::elems(@args);
        my $obj;
        while $i < $n {
            $obj := nqp::atpos(@args, $i);
            unless nqp::iscont_i($obj) || nqp::iscont_n($obj) || nqp::iscont_s($obj) {
                nqp::bindpos(@args, $i, nqp::can($obj, 'cstr')
                    ?? nqp::decont($obj.cstr())
                    !! nqp::decont($obj));
            }
            $i++;
        }
        @args
    }
    $qastcomp.as_mast(QAST::VM.new(
        :moarop('nativecallinvoke'),
        $op[0], $op[1],
        QAST::Op.new(
            :op('call'),
            QAST::WVal.new( :value(nqp::getcodeobj(&decont_all)) ),
            $op[2]
        )));
});
QAST::MASTOperations.add_core_moarop_mapping('nativecallrefresh', 'nativecallrefresh', 0, :decont(0));
QAST::MASTOperations.add_core_moarop_mapping('nativecallcast', 'nativecallcast');
QAST::MASTOperations.add_core_moarop_mapping('nativecallglobal', 'nativecallglobal');
QAST::MASTOperations.add_core_moarop_mapping('nativecallsizeof', 'nativecallsizeof', :decont(0));

QAST::MASTOperations.add_core_moarop_mapping('getcodelocation', 'getcodelocation', :decont(0));

QAST::MASTOperations.add_core_moarop_mapping('uname', 'uname');

# process related opcodes
QAST::MASTOperations.add_core_moarop_mapping('exit', 'exit', 0);
QAST::MASTOperations.add_core_moarop_mapping('sleep', 'sleep', 0);
QAST::MASTOperations.add_core_moarop_mapping('getsignals', 'getsignals');
QAST::MASTOperations.add_core_moarop_mapping('getenvhash', 'getenvhash');
QAST::MASTOperations.add_core_moarop_mapping('getpid', 'getpid');
QAST::MASTOperations.add_core_moarop_mapping('getppid', 'getppid');
QAST::MASTOperations.add_core_moarop_mapping('gethostname', 'gethostname');
QAST::MASTOperations.add_core_moarop_mapping('rand_i', 'rand_i');
QAST::MASTOperations.add_core_moarop_mapping('rand_n', 'randscale_n');
QAST::MASTOperations.add_core_moarop_mapping('srand', 'srand', 0);
QAST::MASTOperations.add_core_moarop_mapping('execname', 'execname');
QAST::MASTOperations.add_core_moarop_mapping('getrusage', 'getrusage');

# thread related opcodes
QAST::MASTOperations.add_core_moarop_mapping('newthread', 'newthread');
QAST::MASTOperations.add_core_moarop_mapping('threadrun', 'threadrun', 0);
QAST::MASTOperations.add_core_moarop_mapping('threadjoin', 'threadjoin', 0);
QAST::MASTOperations.add_core_moarop_mapping('threadid', 'threadid');
QAST::MASTOperations.add_core_moarop_mapping('threadyield', 'threadyield');
QAST::MASTOperations.add_core_moarop_mapping('currentthread', 'currentthread');
QAST::MASTOperations.add_core_moarop_mapping('lock', 'lock', 0);
QAST::MASTOperations.add_core_moarop_mapping('unlock', 'unlock', 0);
QAST::MASTOperations.add_core_moarop_mapping('getlockcondvar', 'getlockcondvar');
QAST::MASTOperations.add_core_moarop_mapping('condwait', 'condwait', 0);
QAST::MASTOperations.add_core_moarop_mapping('condsignalone', 'condsignalone', 0);
QAST::MASTOperations.add_core_moarop_mapping('condsignalall', 'condsignalall', 0);
QAST::MASTOperations.add_core_moarop_mapping('semacquire', 'semacquire');
QAST::MASTOperations.add_core_moarop_mapping('semtryacquire', 'semtryacquire');
QAST::MASTOperations.add_core_moarop_mapping('semrelease', 'semrelease');
QAST::MASTOperations.add_core_moarop_mapping('queuepoll', 'queuepoll');
QAST::MASTOperations.add_core_moarop_mapping('cpucores', 'cpucores');
QAST::MASTOperations.add_core_moarop_mapping('freemem', 'freemem');
QAST::MASTOperations.add_core_moarop_mapping('totalmem', 'totalmem');
QAST::MASTOperations.add_core_moarop_mapping('threadlockcount', 'threadlockcount');
QAST::MASTOperations.add_core_moarop_mapping('setthreadname', 'setthreadname');

# asynchrony related ops
QAST::MASTOperations.add_core_moarop_mapping('timer', 'timer');
QAST::MASTOperations.add_core_moarop_mapping('permit', 'permit', 0);
QAST::MASTOperations.add_core_moarop_mapping('cancel', 'cancel', 0);
QAST::MASTOperations.add_core_moarop_mapping('cancelnotify', 'cancelnotify', 0);
QAST::MASTOperations.add_core_moarop_mapping('signal', 'signal');
QAST::MASTOperations.add_core_moarop_mapping('watchfile', 'watchfile');
QAST::MASTOperations.add_core_moarop_mapping('asyncconnect', 'asyncconnect');
QAST::MASTOperations.add_core_moarop_mapping('asynclisten', 'asynclisten');
QAST::MASTOperations.add_core_moarop_mapping('asyncudp', 'asyncudp');
QAST::MASTOperations.add_core_moarop_mapping('asyncwritebytes', 'asyncwritebytes');
QAST::MASTOperations.add_core_moarop_mapping('asyncwritebytesto', 'asyncwritebytesto');
QAST::MASTOperations.add_core_moarop_mapping('asyncreadbytes', 'asyncreadbytes');
QAST::MASTOperations.add_core_moarop_mapping('spawnprocasync', 'spawnprocasync');
QAST::MASTOperations.add_core_moarop_mapping('killprocasync', 'killprocasync', 1);

# Atomic ops
QAST::MASTOperations.add_core_moarop_mapping('cas', 'cas_o', :decont(1,2));
QAST::MASTOperations.add_core_moarop_mapping('cas_i', 'cas_i');
QAST::MASTOperations.add_core_moarop_mapping('atomicinc_i', 'atomicinc_i');
QAST::MASTOperations.add_core_moarop_mapping('atomicdec_i', 'atomicdec_i');
QAST::MASTOperations.add_core_moarop_mapping('atomicadd_i', 'atomicadd_i');
QAST::MASTOperations.add_core_moarop_mapping('atomicload', 'atomicload_o');
QAST::MASTOperations.add_core_moarop_mapping('atomicload_i', 'atomicload_i');
QAST::MASTOperations.add_core_moarop_mapping('atomicstore', 'atomicstore_o', 1, :decont(1));
QAST::MASTOperations.add_core_moarop_mapping('atomicstore_i', 'atomicstore_i', 1);
QAST::MASTOperations.add_core_moarop_mapping('barrierfull', 'barrierfull');
QAST::MASTOperations.add_core_moarop_mapping('atomicbindattr', 'atomicbindattr_o', 3);
QAST::MASTOperations.add_core_moarop_mapping('casattr', 'casattr_o');

# MoarVM-specific compilation ops
QAST::MASTOperations.add_core_moarop_mapping('iscompunit', 'iscompunit');
QAST::MASTOperations.add_core_moarop_mapping('compunitmainline', 'compunitmainline');
QAST::MASTOperations.add_core_moarop_mapping('compunitcodes', 'compunitcodes');
QAST::MASTOperations.add_core_moarop_mapping('backendconfig', 'backendconfig');

# MoarVM-specific (matching NQP JVM API, though no clone and one-shot only) continuation ops.
QAST::MASTOperations.add_core_moarop_mapping('continuationreset', 'continuationreset');
QAST::MASTOperations.add_core_moarop_mapping('continuationcontrol', 'continuationcontrol');
QAST::MASTOperations.add_core_moarop_mapping('continuationinvoke', 'continuationinvoke');

# MoarVM-specific profiling ops.
QAST::MASTOperations.add_core_moarop_mapping('mvmstartprofile', 'startprofile', 0);
QAST::MASTOperations.add_core_moarop_mapping('mvmendprofile', 'endprofile');

# MoarVM-specific GC ops
QAST::MASTOperations.add_core_moarop_mapping('force_gc', 'force_gc');

# MoarVM-specific coverage ops
QAST::MASTOperations.add_core_moarop_mapping('coveragecontrol', 'coveragecontrol');

# MoarVM-specific configuration program op
QAST::MASTOperations.add_core_moarop_mapping('installconfprog', 'installconfprog');

# MoarVM-specific event subscription op
QAST::MASTOperations.add_core_moarop_mapping('vmeventsubscribe', 'vmeventsubscribe');

# MoarVM-specific specializer plugin ops
QAST::MASTOperations.add_core_moarop_mapping('speshreg', 'speshreg', 2);
QAST::MASTOperations.add_core_moarop_mapping('speshguardtype', 'speshguardtype', 0);
QAST::MASTOperations.add_core_moarop_mapping('speshguardconcrete', 'speshguardconcrete', 0);
QAST::MASTOperations.add_core_moarop_mapping('speshguardtypeobj', 'speshguardtypeobj', 0);
QAST::MASTOperations.add_core_moarop_mapping('speshguardobj', 'speshguardobj', 0);
QAST::MASTOperations.add_core_moarop_mapping('speshguardnotobj', 'speshguardnotobj', 0);
QAST::MASTOperations.add_core_moarop_mapping('speshguardgetattr', 'speshguardgetattr');
QAST::MASTOperations.add_core_op('speshresolve', -> $qastcomp, $op {
    # Get the target name.
    my @args := nqp::clone($op.list);
    my $target_node := nqp::shift(@args);
    unless nqp::istype($target_node, QAST::SVal) {
        nqp::die("speshresolve node must have a first child that is a QAST::SVal");
    }
    my $target := $target_node.value;

    my $regalloc := $*REGALLOC;
    my $frame    := $*MAST_FRAME;
    my $bytecode := $frame.bytecode;

    # Compile the arguments
    my @arg_mast := nqp::list();

    for @args -> $arg {
        if nqp::can($arg, 'flat') && $arg.flat {
            nqp::die('The speshresolve op must not have flattening arguments');
        }
        elsif nqp::can($arg, 'named') && $arg.named {
            nqp::die('The speshresolve op must not have named arguments');
        }
        my $arg_mast := $qastcomp.as_mast($arg, :want($MVM_reg_obj));
        nqp::die("Arg code did not result in a MAST::Local")
            unless $arg_mast.result_reg && $arg_mast.result_reg ~~ MAST::Local;
        nqp::push(@arg_mast, $arg_mast);
    }

    my uint $callsite-id := $frame.callsites.get_callsite_id_from_args(@args, @arg_mast);
    my uint64 $bytecode_pos := nqp::elems($bytecode);

    nqp::writeuint($bytecode, $bytecode_pos, $op_code_prepargs, 5);
    nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $callsite-id, 5);
    $bytecode_pos := $bytecode_pos + 4;

    my uint64 $i := 0;
    for @args -> $arg {
        my $arg_mast := @arg_mast[$i];
        my int $kind := nqp::unbox_i($arg_mast.result_kind);
        my uint64 $arg_opcode := nqp::atpos_i(@kind_to_opcode, $kind);
        nqp::die("Unhandled arg type $kind") unless $arg_opcode;
        nqp::writeuint($bytecode, $bytecode_pos, $arg_opcode, 5);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $i++, 5);
        my uint64 $res_index := nqp::unbox_u($arg_mast.result_reg);
        nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $res_index, 5);
        $bytecode_pos := $bytecode_pos + 6;

        $regalloc.release_register($arg_mast.result_reg, $kind);
    }

    # Assemble the resolve call.
    my $res_reg := $regalloc.fresh_register($MVM_reg_obj);
    nqp::writeuint($bytecode, $bytecode_pos, $op_code_speshresolve, 5);
    my uint $res_index := nqp::unbox_u($res_reg);
    nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 2), $res_index, 5);
    my uint $target_idx := $frame.add-string($target);
    nqp::writeuint($bytecode, nqp::add_i($bytecode_pos, 4), $target_idx, 9);

    MAST::InstructionList.new($res_reg, $MVM_reg_obj)
});

QAST::MASTOperations.add_core_moarop_mapping('hllbool', 'hllbool');
QAST::MASTOperations.add_core_moarop_mapping('hllboolfor', 'hllboolfor');
QAST::MASTOperations.add_core_moarop_mapping('serializetobuf', 'serializetobuf');
QAST::MASTOperations.add_core_moarop_mapping('decodelocaltime', 'decodelocaltime');
QAST::MASTOperations.add_core_moarop_mapping('fork', 'fork');

sub push_op(str $op, *@args) {
    MAST::Op.new_with_operand_array( :$op, @args );
}

QAST::MASTOperations.add_core_op('js', -> $qastcomp, $op {
    $qastcomp.as_mast(QAST::Op.new( :op('die'), QAST::SVal.new( :value('Running JS NYI on MoarVM') )))
});

# vim: ft=perl6 expandtab sw=4
