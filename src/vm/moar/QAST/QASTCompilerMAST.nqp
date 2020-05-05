# Per-compilation instance of the MAST compiler, holding state and driving the
# compilation.

sub POS($c) {
    return $c - 65      if $c >= 65 && $c < 91;  # A..Z
    return $c - 97 + 26 if $c >= 97 && $c < 123; # a..z
    return $c - 48 + 52 if $c >= 48 && $c < 58;  # 0..9
    return 62 if $c == 43;
    return 63 if $c == 47;
    return -1 if $c == 61;
    nqp::die("Invalid data in base64_decode");
}
sub base64_decode(str $s) {
    my $data := MAST::Bytecode.new;
    my @n := (-1, -1, -1, -1);

    my int $len := nqp::chars($s);
    if $len % 4 {
        nqp::die("Length of input to base64_decode is not a multiple of 4");
    }

    my int $pos := 0;
    while $pos < $len {
        @n[0] := POS(nqp::getcp_s($s, $pos++));
        @n[1] := POS(nqp::getcp_s($s, $pos++));
        @n[2] := POS(nqp::getcp_s($s, $pos++));
        @n[3] := POS(nqp::getcp_s($s, $pos++));

        if @n[0] == -1 || @n[1] == -1 || (@n[2] == -1 && @n[3] != -1) {
            nqp::die("Invalid data in base64_decode");
        }

        $data.write_uint8(nqp::bitshiftl_i(@n[0], 2) + nqp::bitshiftr_i(@n[1], 4));
        if @n[2] != -1 {
            $data.write_uint8(nqp::bitshiftl_i(@n[1] +& 15, 4) + nqp::bitshiftr_i(@n[2], 2));
        }
        if @n[3] != -1 {
            $data.write_uint8(nqp::add_i(nqp::bitshiftl_i(@n[2] +& 3, 6), @n[3]));
        }
    }

    return $data;
}

my class MASTCompilerInstance {
    # The HLL that we're compiling.
    has $!hll;

    # The MAST compilation unit we're compiling it into.
    has $!mast_compunit;

    # MAST frames lookup hash.
    has %!mast_frames;

    # The filename we're compiling.
    has $!file;

    # The serialization context of the code we're compiling, if we have one.
    has $!sc;

    # The most recent op we tried to compile, for error reporting.
    has $!last_op;

    has $!writer;

    # This uses a very simple scheme. Write registers are assumed
    # to be write-once, read-once.  Therefore, if a QAST control
    # structure wants to reuse the intermediate result of an
    # expression, it must `set` the result to other registers before
    # using the result as an arg to another op.
    my class RegAlloc {
        has $!frame;
        has @!released;
        has @!released_indexes;

        my @types := [nqp::null,int8,int16,int32,int,num32,num,str,NQPMu,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,uint8,uint16,uint32,uint64];
        method new($frame) {
            my $obj := nqp::create(self);
            my @released := [nqp::null,[],[],[],[],[],[],[],[],nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,nqp::null,[],[],[],[]];
            nqp::bindattr($obj, RegAlloc, '@!released', @released);
            nqp::bindattr($obj, RegAlloc, '$!frame', $frame);
            nqp::bindattr($obj, RegAlloc, '@!released_indexes', nqp::list_i);
            $obj
        }

        method fresh_i() { self.fresh_register($MVM_reg_int64) }
        method fresh_n() { self.fresh_register($MVM_reg_num64) }
        method fresh_s() { self.fresh_register($MVM_reg_str) }
        method fresh_o() { self.fresh_register($MVM_reg_obj) }

        # QAST::Vars need entirely new MAST::Locals all to themselves,
        # so a Local can't be a non-Var for the first half of a block and
        # then a Var the second half, but then control returns to the first half
        method fresh_register($kind, $new = 0) {
            # set $new to 1 here if you suspect a problem with the allocator,
            # or if you suspect a register is being double-released somewhere.
            # $new := 1;
            my @arr := @!released[$kind];

            if nqp::elems(@arr) && !$new {
                my $reg := nqp::pop(@arr);
                nqp::bindpos_i(@!released_indexes, nqp::unbox_u($reg), 0);
                $reg
            }
            else {
                MAST::Local.new(:index($!frame.add_local(@types[$kind])));
            }
        }

        method release_i($reg) { self.release_register($reg, $MVM_reg_int64) }
        method release_n($reg) { self.release_register($reg, $MVM_reg_num64) }
        method release_s($reg) { self.release_register($reg, $MVM_reg_str) }
        method release_o($reg) { self.release_register($reg, $MVM_reg_obj) }

        method release_register($reg, int $kind, int $force = 0) {
            unless $kind == $MVM_reg_void || !$force && $*BLOCK.is_var($reg) {
                nqp::bindpos_i(@!released_indexes, nqp::unbox_u($reg), 1);
                nqp::push(@!released[$kind], $reg);
            }
            NQPMu
        }
    }

    # Holds information about the QAST::Block we're currently compiling.
    my class BlockInfo {
        has $!qast;                 # The QAST::Block
        has $!outer;                # Outer block's BlockInfo
        has %!local_names_by_index; # Locals' names by their indexes
        has %!locals;               # Mapping of local names to locals
        has %!local_kinds;          # Mapping of local registers to kinds
        has %!lexicals;             # Mapping of lexical names to lexicals
        has %!lexical_kinds;        # Mapping of lexical names to kinds
        has %!lexical_params;       # Mapping of lexical param names to their initial result reg
        has %!lexicalrefs;          # Mapping of lexical reference names to lexicals
        has %!lexicalref_kinds;     # Mapping of lexical reference names to kinds
        has int $!param_idx;        # Current lexical parameter index
        has $!compiler;             # The QAST::MASTCompiler
        has @!params;               # List of QAST::Var param nodes
        has $!return_kind;          # Kind of return, tracked while emitting
        has @!captured_inners;      # List of CUIDs of blocks we statically capture
        has %!cloned_inners;        # Mapping of CUIDs of blocks we clone to register with the clone
        has @!contvar_locals;       # Locals with a contvar that needs allocating.

        method new($qast, $outer, $compiler) {
            my $obj := nqp::create(self);
            $obj.BUILD($qast, $outer, $compiler);
            $obj
        }

        method BUILD($qast, $outer, $compiler) {
            $!qast := $qast;
            $!outer := $outer;
            $!compiler := $compiler;
            %!local_names_by_index := nqp::hash();
            %!locals := nqp::hash();
            %!local_kinds := nqp::hash();
            %!lexicals := nqp::hash();
            %!lexical_kinds := nqp::hash();
            %!lexical_params := nqp::hash();
            %!lexicalrefs := nqp::hash();
            %!lexicalref_kinds := nqp::hash();
            @!params := nqp::list();
            @!captured_inners := nqp::list();
            %!cloned_inners := nqp::hash();
            @!contvar_locals := nqp::list();
        }

        method add_param($var) {
            @!params[+@!params] := $var;
            if $var.scope eq 'local' {
                self.register_local($var);
            }
            else {
                my int $res_kind := self.add_lexical($var);
                my $res_reg := $*REGALLOC.fresh_register($res_kind);
                %!lexical_params{$var.name} := $res_reg;
                [$res_kind, $res_reg]
            }
        }

        method add_lexical($var, :$is_static, :$is_cont, :$is_state) {
            my $mf    := $*MAST_FRAME;
            my $type  := $var.returns;
            my $kind  := $!compiler.type_to_register_kind($type);
            my $index := $mf.add_lexical($type, $var.name);
            self.register_lexical($var.name, $index, $kind);
            if $is_static || $is_cont || $is_state {
                my int $flags := $is_static ?? 0 !!
                                 $is_cont   ?? 1 !! 2;
                my $val       := $var.value;
                my $sc        := nqp::getobjsc($val);
                if nqp::isnull($sc) {
                    nqp::die("Object of type " ~ $val.HOW.name($val) ~
                        " in QAST::Var value, but not in SC");
                }
                my int $idx    := nqp::scgetobjidx($sc, $val);
                my int $sc_idx := $!compiler.mast_compunit.sc_idx($sc);
                $mf.add_static_lex_value($index, $flags, $sc_idx, $idx);
            }
            $kind;
        }

        method register_lexical(str $name, $index, $kind) {
            if nqp::existskey(%!lexicals, $name) || nqp::existskey(%!lexicalrefs, $name) {
                nqp::die("Lexical '$name' already declared");
            }
            my $lex := MAST::Lexical.new( :index($index), :frames_out(0) );
            %!lexicals{$name} := $lex;
            %!lexical_kinds{$name} := $kind;
            $lex;
        }

        method add_lexicalref($var) {
            my $mf   := $*MAST_FRAME;
            my $type := $var.returns;
            my $kind := $!compiler.type_to_register_kind($type);
            unless nqp::objprimspec($type) {
                nqp::die("lexicalref declaration must have a native type");
            }
            my $index := $mf.add_lexical(NQPMu, $var.name);
            self.register_lexicalref($var.name, $index, $kind);
            $MVM_reg_obj
        }

        method register_lexicalref(str $name, $index, $kind) {
            if nqp::existskey(%!lexicals, $name) || nqp::existskey(%!lexicalrefs, $name) {
                nqp::die("Lexical '$name' already declared");
            }
            my $lex := MAST::Lexical.new( :index($index), :frames_out(0) );
            %!lexicalrefs{$name} := $lex;
            %!lexicalref_kinds{$name} := $kind;
            $lex;
        }

        method register_local($var, :$is_cont) {
            my $name := $var.name;
            my $temporary := ?$*INSTMT;
            if nqp::existskey(%!locals, $name) ||
                    $temporary && nqp::existskey(%*STMTTEMPS, $name) {
                nqp::die("Local '$name' already declared");
            }
            my $kind := $!compiler.type_to_register_kind($var.returns);
            %!local_kinds{$name} := $kind;
            # pass a 1 meaning get a Totally New MAST::Local
            my $local := $*REGALLOC.fresh_register($kind, !$temporary);
            %!locals{$name} := $local;
            %!local_names_by_index{nqp::unbox_u($local.index)} := $name;
            if $temporary {
                %*STMTTEMPS{$name} := $local;
            }
            if $is_cont {
                nqp::push(@!contvar_locals, $var);
            }
            $local;
        }

        # returns whether a MAST::Local is a variable in this block
        method is_var($local) {
            nqp::existskey(%!local_names_by_index, $local.index)
        }

        method return_kind(*@value) {
            if @value {
                nqp::die("Inconsistent immediate block return type")
                    if ($!qast.blocktype eq 'immediate' || $!qast.blocktype eq 'immediate_static') &&
                        nqp::defined($!return_kind) && @value[0] != $!return_kind;
                $!return_kind := @value[0];
            }
            $!return_kind
        }

        method release_temp($name) {
            my $local := %!locals{$name};
            my $index := $local.index();
            my $kind := %!local_kinds{$name};
            $*REGALLOC.release_register($local, $kind, 1);
            nqp::deletekey(%!local_names_by_index, $index);
            nqp::deletekey(%!locals, $name);
            nqp::deletekey(%!local_kinds, $name);
        }

        method qast() { $!qast }
        method outer() { $!outer }
        method lexical($name) { %!lexicals{$name} }
        method lexicals() { %!lexicals }
        method lexicalref($name) { %!lexicalrefs{$name} }
        method lexicalrefs() { %!lexicalrefs }
        method local($name) { %!locals{$name} }
        method local_kind($name) { %!local_kinds{$name} }
        method lexical_kind($name) { %!lexical_kinds{$name} }
        method lexical_kinds() { %!lexical_kinds }
        method lexicalref_kind($name) { %!lexicalref_kinds{$name} }
        method lexicalref_kinds() { %!lexicalref_kinds }
        method params() { @!params }
        method lexical_param($name) { %!lexical_params{$name} }

        method resolve_lexical($name) {
            my $block := self;
            my $out := 0;
            while $block {
                my $lex := ($block.lexicals()){$name};
                return MAST::Lexical.new( :index($lex.index), :frames_out($out) ) if $lex;
                $out++;
                $block := $block.outer;
            }
            nqp::die("Could not resolve lexical $name");
        }

        method capture_inner($block) {
            nqp::push(@!captured_inners, $block.cuid)
        }
        method clone_inner($block) {
            my $cuid    := $block.cuid;
            my $already := %!cloned_inners{$cuid};
            if $already {
                $already
            }
            else {
                my $reg  := $*REGALLOC.fresh_register($MVM_reg_obj, 1);
                %!cloned_inners{$cuid} := $reg;
                %!local_names_by_index{$reg.index} := $cuid;
                $reg
            }
        }
        method captured_inners() { @!captured_inners }
        method cloned_inners() { %!cloned_inners }

        method contvar_locals() { @!contvar_locals }
    }

    method source_for_node($node) {
        my $source := $node.node
                        ?? ~ nqp::escape($node.node.Str)
                        !! '';
        if nqp::chars($source) > 103 {
            $source := nqp::substr($source, 0, 100) ~ '...';
        }
        if nqp::chars($source) {
            $source := qq[ (source text: "$source")];
        }
        $source;
    }

    my int $serno := 0;
    method unique($prefix = '') { $prefix ~ $serno++ }

    method mast_compunit() { $!mast_compunit }
    method mast_frames() { %!mast_frames }
    method sc() { $!sc }

    method to_mast($qast) {
        # Set up compilation state.
        $!hll := '';
        my %moar := %*COMPILING<moar>;
        my $string-heap := %moar<string-heap>;
        nqp::die("Didn't find a string heap, compiler backend not properly initialized by running stage start?")
            unless $string-heap;
        my $callsites := %moar<callsites>;
        my $annotations;
        if nqp::existskey(%moar, 'annotations') {
            $annotations := %moar<annotations>;
        }
        else {
            $annotations := %moar<annotations> := MAST::Bytecode.new;
        }

        my @frames := nqp::pop(%moar<frames>);
        $!writer := MoarVM::BytecodeWriter.new(:$string-heap, :$callsites, :$annotations);
        $!mast_compunit := MAST::CompUnit.new(
            :$!writer,
            :frames(@frames),
            :sc_handles(%moar<sc_handles>),
            :sc_lookup(%moar<sc_lookup>),
            :extop_sigs(%moar<extop_sigs>),
            :extop_names(%moar<extop_names>),
            :extop_idx(%moar<extop_idx>),
        );
        $!writer.set-compunit($!mast_compunit);
        %!mast_frames := %moar<mast_frames>;
        $!file := nqp::ifnull(nqp::getlexdyn('$?FILES'), "<unknown file>");
        $!sc := NQPMu;

        # Compile, and evaluate to compilation unit.
        self.as_mast($qast);

        # write back our frames to the outer compiler
        if nqp::elems(%moar<frames>) {
            my @outer_frames := %moar<frames>[nqp::elems(%moar<frames>) - 1];
            for @frames {
                $_.clear_index;
                nqp::push(@outer_frames, $_);
            }
        }

        #CATCH {
        #    my $err    := $!;
        #    my $source := self.source_for_node($!last_op);
        #    nqp::die("QAST -> MAST failed while compiling op " ~ $!last_op.op ~ "$source: $err");
        #}

        $!mast_compunit
    }

    method coerce($res, int $desired) {
        my int $got := nqp::unbox_i($res.result_kind);
        if $got != $desired {
            $res.append(self.coercion($res, $desired));
        }
        $res
    }

    # Expects that the value in need of coercing has already been
    # obtained. Produces instructions to coerce it.
    method coercion($res, int $desired) {
        my int $got := nqp::unbox_i($res.result_kind);
        my $reg := $res.result_reg;
        if $got == $desired {
            # Nothing to do.
        }
        elsif $desired == $MVM_reg_void {
            $reg := MAST::VOID;
        }
        elsif $desired == $MVM_reg_obj {
            # See if we already have full-width native.
            if $got == $MVM_reg_int64 || $got == $MVM_reg_num64 ||
                    $got == $MVM_reg_str || $got == $MVM_reg_void ||
                    $got == $MVM_reg_uint64 {
                return QAST::MASTOperations.box(self, $!hll, $got, $reg);
            }
            elsif $got == $MVM_reg_num32 {
                my $grow := self.coercion($res, $MVM_reg_num64);
                my $box := QAST::MASTOperations.box(self, $!hll, $MVM_reg_num64,
                    $grow.result_reg);
                $reg := $box.result_reg;
            }
            elsif $got == $MVM_reg_int32 || $got == $MVM_reg_int16 || $got == $MVM_reg_int8 {
                my $grow := self.coercion($res, $MVM_reg_int64);
                my $box := QAST::MASTOperations.box(self, $!hll, $MVM_reg_int64,
                    $grow.result_reg);
                $reg := $box.result_reg;
            }
            elsif $got == $MVM_reg_uint32 || $got == $MVM_reg_uint16 || $got == $MVM_reg_uint8 {
                my $grow := self.coercion($res, $MVM_reg_uint64);
                my $box := QAST::MASTOperations.box(self, $!hll, $MVM_reg_uint64,
                    $grow.result_reg);
                $reg := $box.result_reg;
            }
            else {
                nqp::die("Unknown boxing case; got: " ~ $got);
            }
        }
        elsif $got == $MVM_reg_obj {
            # See if we want a full-width native.
            if $desired == $MVM_reg_int64 || $desired == $MVM_reg_num64 ||
                    $desired == $MVM_reg_str || $desired == $MVM_reg_uint64 {
                return QAST::MASTOperations.unbox(self, $!hll, $desired, $reg);
            }
            elsif $desired == $MVM_reg_num32 {
                my $unbox := QAST::MASTOperations.unbox(self, $!hll, $MVM_reg_num64, $reg);
                my $shrink := self.coercion($unbox, $desired);
                $reg := $shrink.result_reg;
            }
            elsif $desired == $MVM_reg_int32 || $desired == $MVM_reg_int16 || $desired == $MVM_reg_int8 {
                my $unbox := QAST::MASTOperations.unbox(self, $!hll, $MVM_reg_int64, $reg);
                my $shrink := self.coercion($unbox, $desired);
                $reg := $shrink.result_reg;
            }
            elsif $desired == $MVM_reg_uint32 || $desired == $MVM_reg_uint16 || $desired == $MVM_reg_uint8 {
                my $unbox := QAST::MASTOperations.unbox(self, $!hll, $MVM_reg_uint64, $reg);
                my $shrink := self.coercion($unbox, $desired);
                $reg := $shrink.result_reg;
            }
            else {
                nqp::die("Unknown unboxing case; desired: " ~ $desired);
            }
        }
        else {
            my $res_reg := $*REGALLOC.fresh_register($desired);
            my int $release_type := $got;
            if $desired == $MVM_reg_int64 {
                if $got == $MVM_reg_num64 {
                    %core_op_generators{'coerce_ni'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_str {
                    %core_op_generators{'coerce_si'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_void {
                    %core_op_generators{'const_i64'}($res_reg, 0);
                }
                elsif $got == $MVM_reg_int32 {
                    %core_op_generators{'extend_i32'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_int16 {
                    %core_op_generators{'extend_i16'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_int8 {
                    %core_op_generators{'extend_i8'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_uint64 {
                    %core_op_generators{'coerce_ui'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_uint32 || $got == $MVM_reg_uint16 || $got == $MVM_reg_uint8 {
                    my $uint64 := self.coercion($res, $MVM_reg_uint64);
                    $reg := $uint64.result_reg;
                    $release_type := nqp::unbox_i($uint64.result_kind);
                    %core_op_generators{'coerce_ui'}($res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for int; got: "~$got);
                }
            }
            elsif $desired == $MVM_reg_num64 {
                if $got == $MVM_reg_int64 {
                    %core_op_generators{'coerce_in'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_str {
                    %core_op_generators{'coerce_sn'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_num32 {
                    %core_op_generators{'extend_n32'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_void {
                    %core_op_generators{'const_n64'}($res_reg, 0);
                }
                elsif $got == $MVM_reg_int32 || $got == $MVM_reg_int16 || $got == $MVM_reg_int8 || $got == $MVM_reg_uint32 || $got == $MVM_reg_uint16 || $got == $MVM_reg_uint8 {
                    my $int64 := self.coercion($res, $MVM_reg_int64);
                    $reg := $int64.result_reg;
                    $release_type := nqp::unbox_i($int64.result_kind);
                    push_op('coerce_in', $res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for num; got: "~$got);
                }
            }
            elsif $desired == $MVM_reg_str {
                if $got == $MVM_reg_int64 {
                    %core_op_generators{'coerce_is'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_int32 || $got == $MVM_reg_int16 || $got == $MVM_reg_int8 || $got == $MVM_reg_uint32 || $got == $MVM_reg_uint16 || $got == $MVM_reg_uint8 {
                    my $int64 := self.coercion($res, $MVM_reg_int64);
                    $reg := $int64.result_reg;
                    $release_type := nqp::unbox_i($int64.result_kind);
                    push_op('coerce_is', $res_reg, $reg);
                }
                elsif $got == $MVM_reg_num64 {
                    %core_op_generators{'coerce_ns'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_void {
                    %core_op_generators{'const_s'}($res_reg, '');
                }
                elsif $got == $MVM_reg_uint64 {
                    %core_op_generators{'coerce_us'}($res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for str; got: "~$got);
                }
            }
            elsif $desired == $MVM_reg_num32 {
                if $got == $MVM_reg_num64 {
                    %core_op_generators{'trunc_n32'}($res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for num32; got: "~$got);
                }
            }
            elsif $desired == $MVM_reg_int32 {
                if $got == $MVM_reg_int64 {
                    %core_op_generators{'trunc_i32'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_num64 {
                    my $int64 := self.coercion($res, $MVM_reg_int64);
                    $reg := $int64.result_reg;
                    $release_type := nqp::unbox_i($int64.result_kind);
                    push_op('trunc_i32', $res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for int32; got: " ~ $got);
                }
            }
            elsif $desired == $MVM_reg_int16 {
                if $got == $MVM_reg_int64 {
                    %core_op_generators{'trunc_i16'}($res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for int16; got: " ~ $got);
                }
            }
            elsif $desired == $MVM_reg_int8 {
                if $got == $MVM_reg_int64 {
                    %core_op_generators{'trunc_i8'}($res_reg, $reg);
                }
                else {
                    nqp::die("Unknown coercion case for int8; got: " ~ $got);
                }
            }
            elsif $desired == $MVM_reg_uint64 {
                if $got == $MVM_reg_uint32 {
                    %core_op_generators{'extend_u32'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_uint16 {
                    %core_op_generators{'extend_u16'}($res_reg, $reg);
                }
                elsif $got == $MVM_reg_uint8 {
                    %core_op_generators{'extend_u8'}($res_reg, $reg);
                }
                else {
                    unless $got == $MVM_reg_int64 {
                        my $int64 := self.coercion($res, $MVM_reg_int64);
                        $reg := $int64.result_reg;
                        $release_type := nqp::unbox_i($int64.result_kind);
                    }
                    %core_op_generators{'coerce_iu'}($res_reg, $reg);
                }
            }
            elsif $desired == $MVM_reg_uint32 {
                unless $got == $MVM_reg_uint64 {
                    my $uint64 := self.coercion($res, $MVM_reg_uint64);
                    $reg := $uint64.result_reg;
                    $release_type := nqp::unbox_i($uint64.result_kind);
                }
                %core_op_generators{'trunc_u32'}($res_reg, $reg);
            }
            elsif $desired == $MVM_reg_uint16 {
                unless $got == $MVM_reg_uint64 {
                    my $uint64 := self.coercion($res, $MVM_reg_uint64);
                    $reg := $uint64.result_reg;
                    $release_type := nqp::unbox_i($uint64.result_kind);
                }
                %core_op_generators{'trunc_u16'}($res_reg, $reg);
            }
            elsif $desired == $MVM_reg_uint8 {
                unless $got == $MVM_reg_uint64 {
                    my $uint64 := self.coercion($res, $MVM_reg_uint64);
                    $reg := $uint64.result_reg;
                    $release_type := nqp::unbox_i($uint64.result_kind);
                }
                %core_op_generators{'trunc_u8'}($res_reg, $reg);
            }
            else {
                nqp::die("Coercion from type '$got' to '$desired' NYI");
            }
            $*REGALLOC.release_register($reg, $release_type);
            $reg := $res_reg;
        }
        MAST::InstructionList.new($reg, $desired)
    }

    method as_mast($qast, :$want, :$want-decont) {
        my $*WANT;
        my $*WANT-DECONT := $want-decont;
        if nqp::defined($want) {
            $*WANT := $want;
            if nqp::istype($qast, QAST::Want) {
                self.coerce(self.compile_node(want($qast, $want), :$want), $want)
            }
            else {
                self.coerce(self.compile_node($qast, :$want), $want)
            }
        }
        else {
            self.compile_node($qast)
        }
    }

    sub want($node, $type) {
        my @possibles := $node.list;
        my $best      := nqp::atpos(@possibles, 0);
        if $type != $MVM_reg_obj {
            my $char := $type == $MVM_reg_void  ?? 'v' !!
                        $type == $MVM_reg_int64 ?? 'I' !!
                        $type == $MVM_reg_num64 ?? 'N' !!
                        $type == $MVM_reg_str   ?? 'S' !!
                                                   'X';
            my int $i := 1;
            my int $n := nqp::elems(@possibles);
            while $i < $n {
                if nqp::index(nqp::atpos(@possibles, $i), $char) >= 0 {
                    $best := nqp::atpos(@possibles, $i + 1);
                    last;
                }
                $i := $i + 2;
            }
        }
        $best
    }

    my @return_opnames := [
        'return',
        'return_i',
        'return_i',
        'return_i',
        'return_i',
        'return_n',
        'return_n',
        'return_s',
        'return_o'
    ];

    my @type_initials := [
        '', 'i', 'i', 'i', 'i', 'n', 'n', 's', 'o'
    ];

    my @attr_opnames := [
        '',
        'attr_i',
        'attr_i',
        'attr_i',
        'attr_i',
        'attr_n',
        'attr_n',
        'attr_s',
        'attr_o'
    ];

    my @attrref_opnames := [
        '',
        'getattrref_i',
        'getattrref_i',
        'getattrref_i',
        'getattrref_i',
        'getattrref_n',
        'getattrref_n',
        'getattrref_s',
        '', '',  '',  '',  '',  '',  '',  '',  '',
        # XXX Want a getattrref_u in the end
        'getattrref_i',
        'getattrref_i',
        'getattrref_i',
        'getattrref_i'
    ];

    my @kind_to_op_slot := [
        0, 0, 0, 0, 0, 1, 1, 2, 3, -1, -1, -1, -1, -1, -1, -1, -1, 4, 4, 4, 4
    ];

    my @param_opnames := [
        'param_rp_i',
        'param_rp_n',
        'param_rp_s',
        'param_rp_o',
        'param_rp_u',
        'param_op_i',
        'param_op_n',
        'param_op_s',
        'param_op_o',
        'param_op_u',
        'param_rn_i',
        'param_rn_n',
        'param_rn_s',
        'param_rn_o',
        'param_rn_u',
        'param_on_i',
        'param_on_n',
        'param_on_s',
        'param_on_o',
        'param_on_u',
        'param_rn2_i',
        'param_rn2_n',
        'param_rn2_s',
        'param_rn2_o',
        'param_rn2_u',
        'param_on2_i',
        'param_on2_n',
        'param_on2_s',
        'param_on2_o',
        'param_on2_u'
    ];

    my @return_types := [ NQPMu, int, int, int, int, num, num, str, NQPMu ];

    method register_kind_to_type($kind) { @return_types[$kind] }

    proto method compile_node($node, :$want) { * }

    multi method compile_node(QAST::CompUnit $cu, :$want) {
        # Should have a single child
        if nqp::elems(@($cu)) != 1 {
            nqp::die("QAST::CompUnit should have 1 child, got "
                ~ nqp::elems(@($cu)));
        }

        # Which is the outer block.
        if !nqp::istype($cu[0], QAST::Block) {
            nqp::die("QAST::CompUnit should have 1 child that is a QAST::Block, got " ~ $cu[0].HOW.name($cu[0]));
        }

        # Set HLL and serialization context.
        if $cu.hll {
            $!hll := $cu.hll;
            $!mast_compunit.hll($!hll);
        }
        if $cu.sc {
            $!sc := $cu.sc;
        }

        # Blocks we've seen while compiling.
        my %*BLOCKS_DONE;

        # Compile the block; make sure $*BLOCK is clear.
        my $*BLOCK;
        self.as_mast($cu[0]);

        # If we are in compilation mode, or have pre-deserialization or
        # post-deserialization tasks, handle those. Overall, the process
        # is to desugar this into simpler QAST nodes, then compile those.
        my $is_nested := $cu.is_nested;
        my $comp_mode := $cu.compilation_mode;
        my @pre_des   := $cu.pre_deserialize;
        my @post_des  := $cu.post_deserialize;
        if $comp_mode || @pre_des || @post_des {
            # Create a block into which we'll install all of the other
            # pieces.
            my $block := QAST::Block.new( :blocktype('raw'), :name('<dependencies+deserialize>') );

            # Add pre-deserialization tasks, each as a QAST::Stmt.
            for @pre_des {
                $block.push(QAST::Stmt.new($_));
            }

            # If we need to do deserialization, emit code for that.
            if $comp_mode && !$is_nested {
                $block.push(self.deserialization_code($cu.sc(), $cu.code_ref_blocks(),
                    $cu.repo_conflict_resolver()));
            }

            # Provided we have a serialization context,, pop it off the
            # compiling SC stack.
            unless $is_nested {
                nqp::popcompsc() if $cu.sc;
            }

            # Add post-deserialization tasks.
            for @post_des {
                $block.push(QAST::Stmt.new($_));
            }

            # Compile to MAST and register this block as the deserialization
            # handler.
            self.as_mast($block);
            $!mast_compunit.deserialize_frame(%!mast_frames{$block.cuid});
        }

        # Compile and include load-time logic, if any.
        if nqp::defined($cu.load) {
            my $load_block := QAST::Block.new(
                :blocktype('raw'), :name('<load>'),
                $cu.load
            );
            self.as_mast($load_block);
            $!mast_compunit.load_frame(%!mast_frames{$load_block.cuid});
        }

        # Compile and include main-time logic, if any, and wrap it up so that we
        # pass command line arguments.
        if nqp::defined($cu.main) {
            my $main_block := QAST::Block.new(
                :blocktype('raw'), :name('<entry>'),
                QAST::Op.new(
                    :op('call'),
                    QAST::Block.new(
                        :blocktype('declaration'), :name('<main>'),
                        $cu.main
                    ),
                    QAST::VM.new( :moarop('clargs'), :flat(1) )
                ));
            self.as_mast($main_block);
            $!mast_compunit.main_frame(%!mast_frames{$main_block.cuid});
        }

        $!mast_compunit.mainline_frame(%!mast_frames{$cu[0].cuid});
    }

    # This method is a hook point so that we can override serialization when cross-compiling
    method serialize_sc($sc) {
        my $sh := $!mast_compunit.writer.string-heap.orig-strings;
        my $serialized := nqp::serializetobuf($sc, $sh, MAST::Bytecode);
        [$serialized, $sh, 0]; # change to 1 when you need string heap deserialization
    }

    method deserialization_code($sc, @code_ref_blocks, $repo_conf_res) {
        my $sc_tuple := self.serialize_sc($sc);
        my $serialized := $sc_tuple[0];
        my $sh := $sc_tuple[1];

        $!mast_compunit.serialized($serialized);
        $!mast_compunit.add_strings($sh);

        # String heap QAST.
        my $sh_ast;

        if $sc_tuple[2] {
            $sh_ast := QAST::Op.new( :op('list_s') );
            my $sh_elems := nqp::elems($sh);
            my $i := 0;
            while $i < $sh_elems {
                $sh_ast.push(nqp::isnull_s(nqp::atpos_s($sh, $i))
                    ?? QAST::Op.new( :op('null_s') )
                    !! QAST::SVal.new( :value(nqp::atpos_s($sh, $i)) ));
                $i := $i + 1;
            }
        }
        else {
            $sh_ast := QAST::Op.new( :op('null') );
        }

        # Code references.
        my $cr_ast := QAST::Op.new( :op('list_b'), |@code_ref_blocks );

        # Handle repossession conflict resolution code, if any.
        if $repo_conf_res {
            $repo_conf_res.push(QAST::Var.new( :name('conflicts'), :scope('local') ));
        }
        else {
            $repo_conf_res := QAST::Op.new(
                :op('die_s'),
                QAST::SVal.new( :value('Repossession conflicts occurred during deserialization') )
            );
        }

        # Overall deserialization QAST.
        QAST::Stmts.new(
            QAST::Op.new(
                :op('bind'),
                QAST::Var.new( :name('cur_sc'), :scope('local'), :decl('var') ),
                QAST::Op.new( :op('createsc'), QAST::SVal.new( :value(nqp::scgethandle($sc)) ) )
            ),
            QAST::Op.new(
                :op('scsetdesc'),
                QAST::Var.new( :name('cur_sc'), :scope('local') ),
                QAST::SVal.new( :value(nqp::scgetdesc($sc)) )
            ),
            QAST::Op.new(
                :op('bind'),
                QAST::Var.new( :name('conflicts'), :scope('local'), :decl('var') ),
                QAST::Op.new( :op('list') )
            ),
            QAST::Op.new(
                :op('deserialize'),
                QAST::Op.new( :op('null_s') ),
                QAST::Var.new( :name('cur_sc'), :scope('local') ),
                $sh_ast, # XXX I had to leave this in, otherwise the JS backend doesn't build.
                         #     I would love some help figuring out why!
                QAST::Block.new( :blocktype('immediate'), $cr_ast ),
                QAST::Var.new( :name('conflicts'), :scope('local') )
            ),
            QAST::Op.new(
                :op('if'),
                QAST::Op.new(
                    :op('elems'),
                    QAST::Var.new( :name('conflicts'), :scope('local') )
                ),
                $repo_conf_res
            )
        )
    }

    multi method compile_node(QAST::Block $node, :$want) {
        my $cuid := $node.cuid();
        my $block;
        my $outer;
        #my $*MAST_FRAME;
        if %*BLOCKS_DONE{$cuid} -> @already {
            $block := @already[0];
            $outer := @already[1];
            #$*MAST_FRAME := %!mast_frames{$cuid};
        }
        else {
            my $outer_frame := try $*MAST_FRAME;

            # Create an empty frame and add it to the compilation unit.
            my $frame := MAST::Frame.new(
                :name($node.name),
                :cuuid($cuid),
                :writer($!writer),
                :compunit($!mast_compunit));

            $!mast_compunit.add_frame($frame);
            try $outer := $*BLOCK;
            $block     := BlockInfo.new($node, (nqp::defined($outer) ?? $outer !! NQPMu), self);
            %*BLOCKS_DONE{$cuid} := [$block, $outer];

            # stash the frame by the block's cuid so other references
            # by this block can find it.
            %!mast_frames{$cuid} := $frame;

            # Set the outer if it exists
            $frame.set_outer($outer_frame)
                if $outer_frame && $outer_frame ~~ MAST::Frame;

            # Set exit handler, thunk, and no-inline flags if needed.
            if $node.has_exit_handler {
                $frame.has_exit_handler(1);
            }
            if $node.is_thunk {
                $frame.is_thunk(1);
            }
            if $node.no_inline {
                $frame.no_inline(1);
            }

            # Set code object, if any.
            my $code_obj := $node.code_object;
            if nqp::isconcrete($code_obj) {
                my $sc := nqp::getobjsc($code_obj);
                if nqp::isnull($sc) {
                    nqp::die("Object of type " ~ $code_obj.HOW.name($code_obj) ~
                        " is QAST::Block code object, but not in SC");
                }
                my int $idx    := nqp::scgetobjidx($sc, $code_obj);
                my int $sc_idx := $!mast_compunit.sc_idx($sc);
                $frame.set_code_object_idxs($sc_idx, $idx);
            }

            # Compile all the substatements.
            my $ins;
            {
                my $*BINDVAL := 0;

                # Create a register allocator for this frame.
                my $*REGALLOC := RegAlloc.new($frame);

                # when we enter a QAST::Stmt, the contextual will be cloned, and the locals of
                # newly declared QAST::Vars of local scope inside the Stmt will be stashed here,
                # so they can be released at the end of the QAST::Stmt in which they were
                # declared.  Inability to declare duplicate names is still enforced, and types are
                # still enforced.
                my %*STMTTEMPS := nqp::hash();
                my $*INSTMT := 0;

                my $*BLOCK := $block;
                my $*MAST_FRAME := $frame;

                my $*WANT;
                if $node.blocktype eq 'immediate' || $node.blocktype eq 'immediate_static' {
                    $*WANT := $want;
                }
                $ins := self.compile_all_the_stmts(@($node));

                # Ensure we return full-width.
                my $ins_result_kind := $ins.result_kind;
                if $ins_result_kind == $MVM_reg_num32 {
                    $ins := self.coerce($ins, $MVM_reg_num64);
                }
                elsif $ins_result_kind == $MVM_reg_int32 || $ins_result_kind == $MVM_reg_int16 ||
                        $ins_result_kind == $MVM_reg_int8 || $ins_result_kind == $MVM_reg_uint64 ||
                        $ins_result_kind == $MVM_reg_uint32 || $ins_result_kind == $MVM_reg_uint16 ||
                        $ins_result_kind == $MVM_reg_uint8 {
                    $ins := self.coerce($ins, $MVM_reg_int64);
                }

                $block.return_kind($ins.result_kind);
                # generate a return statement
                # get the return op name
                my $ret_op := @return_opnames[$ins.result_kind];
                my @ret_args := nqp::list();

                # provide the return arg register if needed
                nqp::push(@ret_args, $ins.result_reg) unless $ret_op eq 'return';

                # fixup the end of this frame's instruction list with the return
                %core_op_generators{$ret_op}(|@ret_args);

                $frame.start_subbuffer;

                # Build up the frame prologue. Start with lexical captures and clones.
                my @pre := nqp::list();
                my $capture_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
                for $block.captured_inners() {
                    %core_op_generators{'getcode'}($capture_reg, %!mast_frames{$_});
                    %core_op_generators{'capturelex'}($capture_reg);
                }
                $*REGALLOC.release_register($capture_reg, $MVM_reg_obj);
                my %cloned_inners := $block.cloned_inners();
                for sorted_keys(%cloned_inners) {
                    my $frame := %!mast_frames{$_};
                    my $reg   := %cloned_inners{$_};
                    %core_op_generators{'getcode'}($reg, $frame);
                    %core_op_generators{'takeclosure'}($reg, $reg);
                }

                # Set up for any contvar locals.
                for $block.contvar_locals() {
                    my $value_mast := self.as_mast(
                        QAST::WVal.new( :value($_.value) ),
                        :want($MVM_reg_obj));
                    %core_op_generators{'clone'}($block.local($_.name), $value_mast.result_reg);
                }

                if $node.custom_args {
                    # The block does the arg processing by itself, so we accept any number
                    # of args here.
                    %core_op_generators{'checkarity'}(0, -1);
                }
                else {
                    # Analyze parameters to get count of required/optional and make sure
                    # all is in order.
                    my $param_index := 0;
                    my int $pos_required := 0;
                    my int $pos_optional := 0;
                    my int $pos_slurpy   := 0;
                    my int $named_slurpy := 0;
                    for $block.params {
                        if $_.slurpy {
                            if $_.named {
                                $named_slurpy := 1
                            }
                            else {
                                if $pos_slurpy {
                                    nqp::die("Only one slurpy positional allowed");
                                }
                                $pos_slurpy := 1;
                            }
                        }
                        elsif nqp::defined($_.named) {
                            # Don't count towards arity or count.
                        }
                        elsif $_.default {
                            if $pos_slurpy {
                                nqp::die("Optional positionals must come before all slurpy positionals");
                            }
                            $pos_optional++;
                        }
                        else {
                            if $pos_optional {
                                nqp::die("Required positionals must come before all optional positionals");
                            }
                            if $pos_slurpy {
                                nqp::die("Required positionals must come before all slurpy positionals");
                            }
                            $pos_required++;
                        }
                    }

                    # check the arity
                    push_op('checkarity',
                        $pos_required,
                        $pos_slurpy ?? -1 !! $pos_required + $pos_optional);

                    # build up instructions to bind the params
                    for $block.params -> $var {
                        my $scope := $var.scope;
                        nqp::die("Param scope must be 'local' or 'lexical', got '$scope'")
                            if $scope ne 'lexical' && $scope ne 'local';

                        my $param_kind := self.type_to_register_kind($var.returns);
                        my $opslot := @kind_to_op_slot[$param_kind];

                        my $opname_index := (nqp::defined($var.named)
                                ?? (nqp::islist($var.named) ?? 20 !! 10)
                                !! 0)
                            + ($var.default ?? 5 !! 0) + $opslot;
                        my $opname := @param_opnames[$opname_index];

                        # what will be put in the value register
                        my $val;
                        my $val2;

                        if $var.slurpy {
                            if $var.named {
                                $opname := "param_sn";
                            }
                            else {
                                $opname := "param_sp";
                            }
                        }
                        elsif nqp::defined($var.named) {
                            my $name := $var.named;
                            if nqp::islist($name) {
                                unless nqp::elems($name) == 2 {
                                    nqp::die("Can only support 1 fallback name for a named parameter, '" ~ $name[0] ~ "' has " ~ nqp::elems($name) - 1);
                                }
                                $val := $name[0];
                                $val2 := $name[1];
                            }
                            else {
                                $val := $name;
                            }
                        }
                        else { # positional
                            $val := $param_index;
                        }

                        # Parameter passing is always at full width. In the best
                        # case the register we target is already full-width, but
                        # if not we need a truncation op.
                        my $targetreg := $scope eq 'lexical'
                            ?? $block.lexical_param($var.name)
                            !! $block.local($var.name);
                        my $valreg;
                        my $valreg_kind;
                        my $truncop;

                        if $param_kind == $MVM_reg_obj || $param_kind == $MVM_reg_int64 ||
                                $param_kind == $MVM_reg_num64 || $param_kind == $MVM_reg_str ||
                                $param_kind == $MVM_reg_uint64 {
                            $valreg_kind := $param_kind;
                            $valreg := $targetreg;
                        }
                        elsif $param_kind == $MVM_reg_num32 {
                            $valreg_kind := $MVM_reg_num64;
                            $truncop := 'trunc_n32';
                        }
                        elsif $param_kind == $MVM_reg_int32 {
                            $valreg_kind := $MVM_reg_int64;
                            $truncop := 'trunc_i32';
                        }
                        elsif $param_kind == $MVM_reg_int16 {
                            $valreg_kind := $MVM_reg_int64;
                            $truncop := 'trunc_i16';
                        }
                        elsif $param_kind == $MVM_reg_int8 {
                            $valreg_kind := $MVM_reg_int64;
                            $truncop := 'trunc_i8';
                        }
                        elsif $param_kind == $MVM_reg_uint32 {
                            $valreg_kind := $MVM_reg_uint64;
                            $truncop := 'trunc_u32';
                        }
                        elsif $param_kind == $MVM_reg_uint16 {
                            $valreg_kind := $MVM_reg_uint64;
                            $truncop := 'trunc_u16';
                        }
                        elsif $param_kind == $MVM_reg_uint8 {
                            $valreg_kind := $MVM_reg_uint64;
                            $truncop := 'trunc_u8';
                        }

                        # Get a fresh register to store the result of the
                        # truncation, but only if needed
                        if $valreg_kind != $param_kind {
                            $valreg := $*REGALLOC.fresh_register($valreg_kind);
                        }

                        # NQP->QAST always provides a default value for optional NQP params
                        # even if no default initializer expression is provided.
                        if $var.default {
                            # generate end label to skip initialization code
                            my $endlbl := MAST::Label.new();

                            # emit param grabbing op
                            $val2
                                ?? push_op($opname, $valreg, $val, $val2, $endlbl)
                                !! push_op($opname, $valreg, $val, $endlbl);

                            # generate default initialization code. Could also be
                            # wrapped in another QAST::Block.
                            my $default_mast := self.as_mast($var.default, :want($valreg_kind));

                            # put the initialization result in the variable register
                            op_set($valreg, $default_mast.result_reg);
                            $*REGALLOC.release_register($default_mast.result_reg, nqp::unbox_i($default_mast.result_kind));

                            # end label to skip initialization code
                            $*MAST_FRAME.add-label($endlbl);
                        }
                        elsif $var.slurpy {
                            if $var.named {
                                push_op($opname, $valreg);
                            }
                            else {
                                push_op($opname, $valreg, $pos_required + $pos_optional);
                            }
                        }
                        else {
                            # emit param grabbing op
                            $val2
                                ?? push_op($opname, $valreg, $val, $val2)
                                !! push_op($opname, $valreg, $val);
                        }

                        if $truncop {
                            push_op($truncop, $targetreg, $valreg);
                        }

                        if $scope eq 'lexical' {
                            # emit the op to bind the lexical to the result register
                            %core_op_generators{'bindlex'}($block.lexical($var.name), $targetreg);
                        }

                        # Emit any additional tasks and typechecks.
                        for $var.list {
                            if nqp::istype($_, QAST::ParamTypeCheck) {
                                my $tc_mast := self.as_mast($_[0], :want($MVM_reg_int64));
                                %core_op_generators{'assertparamcheck'}($tc_mast.result_reg);
                                $*REGALLOC.release_register($tc_mast.result_reg, $MVM_reg_int64);
                            }
                            else {
                                self.as_mast($_, :want($MVM_reg_void));
                            }
                        }

                        $param_index++;
                    }

                    # If we didn't slurp all the names, check there are no
                    # unexpected ones.
                    push_op('paramnamesused') unless $named_slurpy;
                }
                my $subbuffer := $frame.end_subbuffer;
                $frame.insert_bytecode($subbuffer, 0);
            }

            # Set up debug symbols in the MAST::Frame.
            my %debug_map := $node.local_debug_map();
            for sorted_keys(%debug_map) -> $key {
                my $value := %debug_map{$key};
                my $local_idx := $block.local($key);
                if nqp::isconcrete($local_idx) {
                    $frame.add_local_debug_name($value, $local_idx);
                }
            }
        }

        if $node.blocktype eq 'raw' || !nqp::istype($outer, BlockInfo) {
            MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
        }
        elsif $node.blocktype eq 'immediate' {
            my $clone_reg := $*BLOCK.clone_inner($node);
            if nqp::defined($want) && $want == $MVM_reg_void {
                $*MAST_FRAME.compile-simple-call($clone_reg, nqp::null);
                MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
            }
            else {
                my $res_reg   := $*REGALLOC.fresh_register($block.return_kind);
                $*MAST_FRAME.compile-simple-call($clone_reg, $res_reg);
                MAST::InstructionList.new($res_reg, $block.return_kind)
            }
        }
        elsif $node.blocktype eq 'immediate_static' {
            $*BLOCK.capture_inner($node);
            my $code_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
            %core_op_generators{'getcode'}($code_reg, %!mast_frames{$node.cuid});
            if nqp::defined($want) && $want == $MVM_reg_void {
                $*MAST_FRAME.compile-simple-call($code_reg, nqp::null);
                MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
            } else {
                my $res_reg  := $*REGALLOC.fresh_register($block.return_kind);
                $*MAST_FRAME.compile-simple-call($code_reg, $res_reg);
                MAST::InstructionList.new($res_reg, $block.return_kind)
            }
        }
        elsif $node.blocktype eq '' || $node.blocktype eq 'declaration' {
            my $clone_reg := $*BLOCK.clone_inner($node);
            MAST::InstructionList.new($clone_reg, $MVM_reg_obj)
        }
        elsif $node.blocktype eq 'declaration_static' {
            $*BLOCK.capture_inner($node);
            if nqp::defined($want) && $want == $MVM_reg_void {
                my $code_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
                %core_op_generators{'getcode'}($code_reg, %!mast_frames{$node.cuid});
                MAST::InstructionList.new($code_reg, $MVM_reg_obj)
            }
            else {
                my $clone_reg := $*BLOCK.clone_inner($node);
                MAST::InstructionList.new($clone_reg, $MVM_reg_obj)
            }
        }
        else {
            nqp::die("Unhandled blocktype " ~ $node.blocktype);
        }
    }

    multi method compile_node(QAST::Stmts $node, :$want) {
        self.compile_annotation($node);
        my $resultchild := $node.resultchild;
        nqp::die("resultchild out of range, max allowed is "
            ~ nqp::elems(@($node)) - 1 ~ ", got $resultchild")
        if (nqp::defined($resultchild) && $resultchild >= nqp::elems(@($node)));
        self.compile_all_the_stmts(@($node), $resultchild)
    }

    multi method compile_node(QAST::Stmt $node, :$want) {
        self.compile_annotation($node);
        my %stmt_temps := nqp::clone(%*STMTTEMPS); # guaranteed to be initialized
        my $result     := self.compile_with_stmt_temps($node, %stmt_temps);
        for sorted_keys(%stmt_temps) -> $temp_key {
            if !nqp::existskey(%*STMTTEMPS, $temp_key) &&
                    !nqp::eqaddr($*BLOCK.local($temp_key), $result.result_reg) {
                $*BLOCK.release_temp($temp_key);
            }
        }
        $result
    }
    method compile_with_stmt_temps($node, %stmt_temps) {
        my %*STMTTEMPS  := %stmt_temps;
        my $*INSTMT     := 1;
        my $resultchild := $node.resultchild;
        nqp::die("resultchild out of range, max allowed is "
            ~ nqp::elems(@($node)) - 1 ~ ", got $resultchild")
        if (nqp::defined($resultchild) && $resultchild >= nqp::elems(@($node)));
        self.compile_all_the_stmts(@($node), $resultchild);
    }

    method compile_annotation($qast) {
        my $node := $qast.node;
        if nqp::isconcrete($node) && nqp::can($node,'orig') {
            my @line_file := HLL::Compiler.linefileof($node.orig(), $node.from(), :cache(1), :directives(1));
            my $line := @line_file[0];
            my $file := @line_file[1] || $!file;
            MAST::Annotated.new(:$file, :$line);
        }
    }

    # This takes any node that is a statement list of some kind and compiles
    # all of the statements within it.
    method compile_all_the_stmts(@stmts, $resultchild?) {
        # the most recent statement mast
        my $last_stmt;
        my $result_stmt;
        my $result_count := 0;
        $resultchild := $resultchild // -1;
        my $final_stmt_idx := +@stmts - 1;
        my $WANT := $*WANT;
        my $all_void := nqp::defined($WANT) && $WANT == $MVM_reg_void;
        for @stmts {
            my int $use_result := 0;
            # Compile this child to MAST, and add its instructions to the end
            # of our instruction list. Also track the last statement.
            # if this is the statement we've been asked to make the result
            if !$all_void && ($result_count == $resultchild
            # or if we weren't given a particular result statement and we're on
            # the last statement,
                    || $resultchild == -1 && $result_count == $final_stmt_idx) {
                # compile $_ with an explicit $want, either what's given or obj
                my $want-decont := $*WANT-DECONT;
                $last_stmt := nqp::defined($WANT)
                    ?? self.as_mast($_, :want($WANT), :$want-decont)
                    !! self.as_mast($_, :$want-decont);
                if nqp::unbox_i($last_stmt.result_kind) == $MVM_reg_void {
                    $last_stmt := self.coerce($last_stmt, $MVM_reg_obj);
                }
                $use_result := 1;
            }
            else {
                $last_stmt := self.as_mast($_, :want($MVM_reg_void));
            }

            if $use_result {
                $result_stmt := $last_stmt;
            }
            else {
                # release top-level results (since they can't be used by anything anyway)
                $*REGALLOC.release_register($last_stmt.result_reg, nqp::unbox_i($last_stmt.result_kind));
            }
            $result_count++;
        }
        if $result_stmt && nqp::unbox_i($result_stmt.result_kind) != $MVM_reg_void {
            MAST::InstructionList.new($result_stmt.result_reg, nqp::unbox_i($result_stmt.result_kind));
        }
        else {
            MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
        }
    }

    multi method compile_node(QAST::Op $node, :$want) {
        $!last_op := $node;
        QAST::MASTOperations.compile_op(self, $!hll, $node)
    }

    multi method compile_node(QAST::VM $node, :$want) {
        if $node.supports('moar') {
            return nqp::defined($want)
                ?? self.as_mast($node.alternative('moar'), :$want)
                !! self.as_mast($node.alternative('moar'));
        }
        elsif $node.supports('moarop') {
            return nqp::defined($want)
                ?? QAST::MASTOperations.compile_mastop(self, $node.alternative('moarop'), $node.list, [], :$want)
                !! QAST::MASTOperations.compile_mastop(self, $node.alternative('moarop'), $node.list, []);
        }
        elsif $node.supports('mast') {
            return $node.alternative('mast');
        }
        else {
            nqp::die("To compile on the MoarVM backend, QAST::VM must have an alternative 'moar' or 'moarop'");
        }
    }

    sub check_kinds($a, $b) {
        nqp::die("Register types $a and $b don't match") unless $a == $b;
    }

    my @lex_n_opnames := [
        'lex_ni',
        'lex_nn',
        'lex_ns',
        'lex_no',
        'lex_nu'
    ];

    my @lexref_opnames := [
        '',
        'getlexref_i8',
        'getlexref_i16',
        'getlexref_i32',
        'getlexref_i',
        'getlexref_n32',
        'getlexref_n',
        'getlexref_s',
        '', '',  '',  '',  '',  '',  '',  '',  '',
        'getlexref_u8',
        'getlexref_u16',
        'getlexref_u32',
        'getlexref_u'
    ];

    my @lexref_n_opnames := [
        'getlexref_ni',
        'getlexref_nn',
        'getlexref_ns',
        '',
        'getlexref_nu',
    ];

    my @decont_opnames := [
        'decont_i',
        'decont_n',
        'decont_s',
        'decont',
        'decont_u'
    ];

    multi method compile_node(QAST::Var $node, :$want) {
        self.compile_var($node, :$want)
    }

    multi method compile_node(QAST::VarWithFallback $node, :$want) {
        my $var_res := self.compile_var($node, :$want);
        if $*BINDVAL || $var_res.result_kind != $MVM_reg_obj {
            $var_res
        }
        else {
            my $fallback_if_nonnull := MAST::Label.new();
            my $fallback_end := MAST::Label.new();
            my $res_reg := $*REGALLOC.fresh_o();
            %core_op_generators{'ifnonnull'}($var_res.result_reg, $fallback_if_nonnull);

            my $fallback_res := self.as_mast($node.fallback, :want($MVM_reg_obj));
            op_set($res_reg, $fallback_res.result_reg);
            %core_op_generators{'goto'}($fallback_end);
            $*MAST_FRAME.add-label($fallback_if_nonnull);
            op_set($res_reg, $var_res.result_reg);
            $*MAST_FRAME.add-label($fallback_end);
            $*REGALLOC.release_register($var_res.result_reg, $MVM_reg_obj);
            $*REGALLOC.release_register($fallback_res.result_reg, $MVM_reg_obj);

            MAST::InstructionList.new($res_reg, $MVM_reg_obj)
        }
    }

    method compile_var($node, :$want) {
        my $scope := $node.scope;
        my $decl  := $node.decl;

        my $res_reg;
        my int $res_kind;

        # Handle any declarations; after this, we call through to the
        # lookup code.
        if $decl {
            # If it's a parameter, add it to the things we should bind
            # at block entry.
            if $decl eq 'param' {
                if $scope eq 'local' {
                    $*BLOCK.add_param($node);
                }
                elsif $scope eq 'lexical' {
                    my @details := $*BLOCK.add_param($node);
                    $res_kind := @details[0];
                    $res_reg := @details[1];
                }
                else {
                    nqp::die("Parameter cannot have scope '$scope'; use 'local' or 'lexical'");
                }
            }
            elsif $decl eq 'var' {
                if $scope eq 'local' {
                    $*BLOCK.register_local($node);
                }
                elsif $scope eq 'lexical' {
                    $*BLOCK.add_lexical($node);
                }
                elsif $scope eq 'lexicalref' {
                    $*BLOCK.add_lexicalref($node);
                }
                else {
                    nqp::die("Cannot declare variable with scope '$scope'; use one of 'local', 'lexical', or 'lexicalref'");
                }
            }
            elsif $decl eq 'static' {
                if $scope ne 'lexical' {
                    nqp::die("Can only use 'static' decl with scope 'lexical', got scope '$scope'");
                }
                $*BLOCK.add_lexical($node, :is_static);
            }
            elsif $decl eq 'contvar' {
                if $scope eq 'local' {
                    $*BLOCK.register_local($node, :is_cont);
                }
                elsif $scope eq 'lexical' {
                    $*BLOCK.add_lexical($node, :is_cont);
                }
                else {
                    nqp::die("Can only use 'contvar' decl with scope 'lexical' or 'local', got scope '$scope'");
                }
            }
            elsif $decl eq 'statevar' {
                if $scope ne 'lexical' {
                    nqp::die("Can only use 'statevar' decl with scope 'lexical', got scope '$scope'");
                }
                $*BLOCK.add_lexical($node, :is_state);
            }
            else {
                nqp::die("Don't understand declaration type '$decl'");
            }
        }

        # If we know what we're after, some opts:
        if nqp::isconcrete($want) {
            # Declaration in void context need generate no code.
            if $want == $MVM_reg_void {
                return MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
            }

            # Both lexicalref and attributeref in the context we want a
            # non-object devolve to lexical and attribute, since we'd only
            # de-ref right away anyway.
            if $want != $MVM_reg_obj {
                $scope := 'lexical'   if $scope eq 'lexicalref';
                $scope := 'attribute' if $scope eq 'attributeref';
            }
        }

        # If we want a decontainerized value, then we don't ever need a
        # reference in this context either.
        if $*WANT-DECONT {
            $scope := 'lexical'   if $scope eq 'lexicalref';
            $scope := 'attribute' if $scope eq 'attributeref';
        }

        # Now go by scope.
        my $name := $node.name;
        if $scope eq 'local' {
            my $local := $*BLOCK.local($name);
            if $local {
                $res_kind := $*BLOCK.local_kind($name);
                if $*BINDVAL {
                    my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($res_kind));
                    op_set($local, $valmast.result_reg);
                    $*REGALLOC.release_register($valmast.result_reg, $res_kind);
                }
                $res_reg := $local;
            }
            else {
                nqp::die("Cannot reference undeclared local '$name'");
            }
        }
        elsif $scope eq 'lexical' {
            my $lex;
            my $lexref;
            my $outer := 0;
            my $block := $*BLOCK;
            my $must_be_late_bound;
            # find the block where the lexical was declared, if any
            while nqp::istype($block, BlockInfo) {
                last if $block.qast.ann('DYN_COMP_WRAPPER');
                $lex := $block.lexical($name);
                last if $lex;
                $lexref := $block.lexicalref($name);
                last if $lexref;
                $must_be_late_bound := 1 if $block.qast.ann('BEGINISH');
                $block := $block.outer;
                $outer++;
            }
            if $lex && !$must_be_late_bound {
                $res_kind := $block.lexical_kind($name);
                if $outer {
                    # need to create lex that knows how many frames to go out
                    $lex := MAST::Lexical.new( :index($lex.index), :frames_out($outer) );
                }
                if $*BINDVAL {
                    my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($res_kind));
                    $res_reg := $valmast.result_reg;
                    %core_op_generators{'bindlex'}($lex, $res_reg);
                }
                elsif $decl ne 'param' {
                    $res_reg := $*REGALLOC.fresh_register($res_kind);
                    %core_op_generators{'getlex'}($res_reg, $lex);
                }
                else {
                    # for lexical param declarations, we don't actually have a result value,
                    # since the param bindlex may be stale by the time the result register
                    # could be used, since the bindlex always occurs at the very top,
                    # so turn around and release the temp register already preallocated.
                    $*REGALLOC.release_register($res_reg, $res_kind);
                    # get another one in case someone is using it...
                    $res_reg := $*REGALLOC.fresh_register($res_kind);
                    %core_op_generators{'getlex'}($res_reg, $lex);
                }
            }
            elsif $lexref && !$must_be_late_bound{
                if $*BINDVAL {
                    nqp::die('Cannot bind to QAST::Var resolving to a lexicalref');
                }
                $res_kind := $block.lexicalref_kind($name);
                if $outer {
                    $lexref := MAST::Lexical.new( :index($lexref.index), :frames_out($outer) );
                }
                my $tmp_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
                $res_reg := $*REGALLOC.fresh_register($res_kind);
                %core_op_generators{'getlex'}($tmp_reg, $lexref);
                %core_op_generators{@decont_opnames[@kind_to_op_slot[$res_kind]]}($res_reg, $tmp_reg);
                $*REGALLOC.release_register($tmp_reg, $MVM_reg_obj);
            }
            else {
                $res_kind := $lex
                    ?? $block.lexical_kind($name)
                    !! self.type_to_register_kind($node.returns);
                if $*BINDVAL {
                    my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($res_kind));
                    $res_reg := $valmast.result_reg;
                    %core_op_generators{"bind"~@lex_n_opnames[@kind_to_op_slot[$res_kind]]}($name, $res_reg);
                    $res_kind := $valmast.result_kind;
                }
                else {
                    $res_reg := $*REGALLOC.fresh_register($res_kind);
                    %core_op_generators{"get"~@lex_n_opnames[@kind_to_op_slot[$res_kind]]}(
                        $res_reg, $name);
                }
            }
        }
        elsif $scope eq 'lexicalref' {
            my $lex;
            my $lexref;
            my $outer := 0;
            my $block := $*BLOCK;
            # find the block where the lexical was declared, if any
            while nqp::istype($block, BlockInfo) {
                last if $block.qast.ann('DYN_COMP_WRAPPER');
                $lex := $block.lexical($name);
                last if $lex;
                $lexref := $block.lexicalref($name);
                last if $lexref;
                $block := $block.outer;
                $outer++;
            }
            $res_kind := $MVM_reg_obj;
            $res_reg := $*REGALLOC.fresh_register($res_kind);
            if $lex {
                # We need to take a reference to the lexical.
                if $*BINDVAL {
                    nqp::die("Cannot bind to non-reference QAST::Var '{$name}'");
                }
                if $outer {
                    $lex := MAST::Lexical.new( :index($lex.index), :frames_out($outer) );
                }
                my $lex_kind := $block.lexical_kind($name);
                if $lex_kind == $MVM_reg_obj {
                    nqp::die('Cannot take a reference to a non-native lexical');
                }
                %core_op_generators{@lexref_opnames[$lex_kind]}($res_reg, $lex);
            }
            elsif $lexref {
                # We want a reference, the register contains a reference, so
                # just do the lookup.
                if $outer {
                    $lexref := MAST::Lexical.new( :index($lexref.index), :frames_out($outer) );
                }
                if $*BINDVAL {
                    my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($MVM_reg_obj));
                    $res_reg := $valmast.result_reg;
                    %core_op_generators{'bindlex'}($lexref, $res_reg);
                }
                else {
                    %core_op_generators{'getlex'}($res_reg, $lexref);
                }
            }
            else {
                if $*BINDVAL {
                    nqp::die('Cannot bind to late-bound QAST::Var with scope lexicalref');
                }
                my $lex_kind := self.type_to_register_kind($node.returns);
                %core_op_generators{@lexref_n_opnames[@kind_to_op_slot[$lex_kind]]}(
                    $res_reg, $name);
            }
        }
        elsif $scope eq 'typevar' {
            if $*BINDVAL {
                nqp::die('Cannot bind to QAST::Var with scope typevar');
            }
            my $name_reg := $*REGALLOC.fresh_s();
            $res_reg     := $*REGALLOC.fresh_o();
            $res_kind    := $MVM_reg_obj;
            %core_op_generators{'const_s'}($name_reg, $name);
            %core_op_generators{'getlexperinvtype_o'}($res_reg, $name_reg);
            $*REGALLOC.release_register($name_reg, $MVM_reg_str);
        }
        elsif $scope eq 'contextual' {
            my $name_const := const_s($name);
            my $lex := $*BLOCK.lexical($name);
            if $lex {
                # In current frame; do as lexical does.
                $res_kind := $*BLOCK.lexical_kind($name);
                if $*BINDVAL {
                    my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($res_kind));
                    $res_reg := $valmast.result_reg;
                    %core_op_generators{'bindlex'}($lex, $res_reg);
                }
                elsif $decl ne 'param' {
                    $res_reg := $*REGALLOC.fresh_register($res_kind);
                    %core_op_generators{'getlex'}($res_reg, $lex);
                }
                else {
                    $*REGALLOC.release_register($res_reg, $res_kind);
                    $res_reg := $*REGALLOC.fresh_register($res_kind);
                    %core_op_generators{'getlex'}($res_reg, $lex);
                }
            }
            else {
                # Need lookup.
                if $*BINDVAL {
                    my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($MVM_reg_obj));
                    $res_reg := $valmast.result_reg;
                    %core_op_generators{'binddynlex'}($name_const.result_reg, $res_reg);
                }
                else {
                    $res_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
                    %core_op_generators{'getdynlex'}($res_reg, $name_const.result_reg);
                }
            }
            $*REGALLOC.release_register($name_const.result_reg, $MVM_reg_str);
            $res_kind := $MVM_reg_obj;
        }
        elsif $scope eq 'attribute' {
            # Ensure we have object and class handle.
            my @args := $node.list();
            if +@args != 2 {
                nqp::die("An attribute lookup needs 2 args (an object and a class handle), got " ~ +@args);
            }

            # Compile object and handle.
            my $obj := self.as_mast_clear_bindval(@args[0], :want($MVM_reg_obj));
            my $han := self.as_mast_clear_bindval(@args[1], :want($MVM_reg_obj));

            my int $hint := -1;

            if nqp::istype(@args[1], QAST::WVal) {
                $hint := nqp::hintfor(@args[1].value, $name);
            }

            # Go by whether it's a bind or lookup. We always access the
            # attributes at full-width from the VM op interface.
            my $kind := self.type_to_register_kind($node.returns);
            if $kind == $MVM_reg_num32 {
                $kind := $MVM_reg_num64;
            }
            elsif $kind == $MVM_reg_int32 || $kind == $MVM_reg_int16 ||
                    $kind == $MVM_reg_int8 {
                $kind := $MVM_reg_int64;
            }
            elsif $kind == $MVM_reg_uint64 || $kind == $MVM_reg_uint32 ||
                    $kind == $MVM_reg_uint16 || $kind == $MVM_reg_uint8 {
                # For now compile as signed
                $kind := $MVM_reg_int64;
            }
            if $*BINDVAL {
                my $valmast := self.as_mast_clear_bindval($*BINDVAL, :want($kind));
                %core_op_generators{'bind' ~ @attr_opnames[$kind]}($obj.result_reg,
                    $han.result_reg, $name, $valmast.result_reg,
                        $hint);
                $res_reg := $valmast.result_reg;
                $res_kind := $valmast.result_kind;
            }
            else {
                $res_reg := $*REGALLOC.fresh_register($kind);
                $res_kind := $kind;
                %core_op_generators{'get' ~ @attr_opnames[$kind]}($res_reg, $obj.result_reg,
                    $han.result_reg, $name, $hint);
            }
            $*REGALLOC.release_register($obj.result_reg, $MVM_reg_obj);
            $*REGALLOC.release_register($han.result_reg, $MVM_reg_obj);
        }
        elsif $scope eq 'attributeref' {
            # Ensure we have object and class handle, and aren't binding.
            my @args := $node.list();
            if +@args != 2 {
                nqp::die("An attribute reference needs 2 args (an object and a class handle), got" ~ +@args);
            }
            if $*BINDVAL {
                nqp::die("Cannot bind to QAST::Var '{$name}' with scope attributeref");
            }

            # Ensure we've a natively typed attribute to take a ref to.
            my $kind := self.type_to_register_kind($node.returns);
            if $kind == $MVM_reg_obj {
                nqp::die("Attribute references can only be to native types");
            }

            # Compile object and handle, and get hint.
            my $obj := self.as_mast_clear_bindval(@args[0], :want($MVM_reg_obj));
            my $han := self.as_mast_clear_bindval(@args[1], :want($MVM_reg_obj));
            my int $hint := -1;
            if nqp::istype(@args[1], QAST::WVal) {
                $hint := nqp::hintfor(@args[1].value, $name);
            }

            # Emit lookup.
            $res_reg := $*REGALLOC.fresh_register($MVM_reg_obj);
            $res_kind := $MVM_reg_obj;
            %core_op_generators{@attrref_opnames[$kind]}($res_reg, $obj.result_reg,
                $han.result_reg, $name, $hint );
            $*REGALLOC.release_register($obj.result_reg, $MVM_reg_obj);
            $*REGALLOC.release_register($han.result_reg, $MVM_reg_obj);
        }
        elsif $scope eq 'positional' {
            return self.as_mast_clear_bindval($*BINDVAL
                ?? QAST::Op.new( :op('positional_bind'), |$node.list, $*BINDVAL)
                !! QAST::Op.new( :op('positional_get'), |$node.list));
        }
        elsif $scope eq 'associative' {
            return self.as_mast_clear_bindval($*BINDVAL
                ?? QAST::Op.new( :op('associative_bind'), |$node.list, $*BINDVAL)
                !! QAST::Op.new( :op('associative_get'), |$node.list));
        }
        else {
            nqp::die("QAST::Var with scope '$scope' NYI");
        }

        MAST::InstructionList.new($res_reg, $res_kind)
    }

    multi method compile_node(MAST::InstructionList $ilist, :$want) {
        $ilist
    }

    multi method compile_node(MAST::Node $node, :$want) {
        MAST::InstructionList.new(MAST::VOID, $MVM_reg_void)
    }

    method as_mast_clear_bindval($node, :$want) {
        my $*BINDVAL := 0;
        nqp::defined($want) ?? self.as_mast($node, :$want) !! self.as_mast($node)
    }

    proto method as_mast_constant($qast) { * }

    multi method as_mast_constant(QAST::IVal $iv) {
        $iv.value
    }
    multi method as_mast_constant(QAST::SVal $sv) {
        $sv.value
    }
    multi method as_mast_constant(QAST::NVal $nv) {
        $nv.value
    }
    multi method as_mast_constant(QAST::Want $want) {
        my int $finger := 1;
        my @children := $want.list;
        while $finger < nqp::elems(@children) {
            my str $got := @children[$finger];
            if $got eq 'Ss' || $got eq 'Ii' || $got eq 'Nn' {
                return self.as_mast_constant(@children[$finger + 1]);
            }
            $finger := $finger + 2;
        }
        return self.as_mast_constant(@children[0]);
    }
    multi method as_mast_constant(QAST::Op $op) {
        if $op.op eq 'const' && nqp::existskey(%const_map, $op.name) {
            return %const_map{$op.name};
        }
        nqp::die("Expected QAST constant, got op '" ~ $op.op ~ "'");
    }
    multi method as_mast_constant(QAST::Node $qast) {
        nqp::die("Expected QAST constant, got QAST::Node");
    }

    multi method compile_node(QAST::Want $node, :$want) {
        # If we're not in a coercive context, take the default.
        self.as_mast($node[0], :want-decont($*WANT-DECONT))
    }

    multi method compile_node(QAST::IVal $iv, :$want) {
        my $reg := $*REGALLOC.fresh_i();
        MAST::Op.new(
            :op('const_i64'),
            $reg,
            $iv.value
        );
        MAST::InstructionList.new(
            $reg,
            $MVM_reg_int64)
    }

    multi method compile_node(QAST::NVal $nv, :$want) {
        my $reg := $*REGALLOC.fresh_n();
        MAST::Op.new(
            :op('const_n64'),
            $reg,
            $nv.value
        );
        MAST::InstructionList.new(
            $reg,
            $MVM_reg_num64)
    }

    sub const_s($val) {
        my $reg := $*REGALLOC.fresh_s();
        MAST::Op.new(:op('const_s'), $reg, $val);
        MAST::InstructionList.new(
            $reg,
            $MVM_reg_str)
    }

    multi method compile_node(QAST::SVal $sv, :$want) {
        const_s($sv.value)
    }

    multi method compile_node(QAST::BVal $bv, :$want) {
        my $block := $bv.value;
        my $cuid  := $block.cuid();
        my $frame := %!mast_frames{$cuid};
        nqp::die("QAST::Block with cuid $cuid has not appeared")
            unless $frame && $frame ~~ MAST::Frame;

        my $reg := $*REGALLOC.fresh_o();
        MAST::Op.new(
            :op('getcode'),
            $reg,
            $frame
        );
        MAST::InstructionList.new(
            $reg,
            $MVM_reg_obj)
    }

    multi method compile_node(QAST::WVal $node, :$want) {
        if nqp::isconcrete($want) && $want == $MVM_reg_void {
            MAST::InstructionList.new(MAST::VOID, $MVM_reg_void);
        }
        else {
            my $val    := $node.value;
            my $sc     := nqp::getobjsc($val);
            if nqp::isnull($sc) {
                nqp::die("Object of type " ~ $val.HOW.name($val) ~ " in QAST::WVal, but not in SC");
            }
            my $idx    := nqp::scgetobjidx($sc, $val);
            my $sc_idx := $!mast_compunit.sc_idx($sc);
            my $reg    := $*REGALLOC.fresh_o();
            my $op     := $idx < 32768 ?? 'wval' !! 'wval_wide';
            MAST::Op.new(
                :op($op),
                $reg,
                $sc_idx,
                $idx
            );
            MAST::InstructionList.new(
                $reg,
                $MVM_reg_obj)
        }
    }

    multi method compile_node(QAST::Regex $node, :$want) {
        my $rxcomp := QAST::MASTRegexCompiler.new(:qastcomp(self), :regalloc($*REGALLOC));
        nqp::defined($want)
            ?? $rxcomp.as_mast($node, :want($want))
            !! $rxcomp.as_mast($node)
    }

    multi method compile_node($unknown, :$want) {
        nqp::die("Unknown QAST node type " ~ $unknown.HOW.name($unknown));
    }

    method annotated($ilist, $file, $line) {
        nqp::die("annotated got called!");
        MAST::Annotated.new(:file($file), :line($line));
        MAST::InstructionList.new($ilist.result_reg, $ilist.result_kind)
    }

    method type_to_register_kind($type) {
        if nqp::isnull($type) {
            $MVM_reg_obj
        }
        else {
            my int $primspec := nqp::objprimspec($type);
            if $primspec == 0 {
                $MVM_reg_obj
            }
            elsif $primspec == 1 {
                my int $size := nqp::objprimbits($type);
                if nqp::objprimunsigned($type) {
                    if $size == 64    { $MVM_reg_uint64 }
                    elsif $size == 32 { $MVM_reg_uint32 }
                    elsif $size == 16 { $MVM_reg_uint16 }
                    elsif $size == 8  { $MVM_reg_uint8 }
                    else { nqp::die("Unknown uint size $size") }
                }
                else {
                    if $size == 64    { $MVM_reg_int64 }
                    elsif $size == 32 { $MVM_reg_int32 }
                    elsif $size == 16 { $MVM_reg_int16 }
                    elsif $size == 8  { $MVM_reg_int8 }
                    else { nqp::die("Unknown int size $size") }
                }
            }
            elsif $primspec == 2 {
                my int $size := nqp::objprimbits($type);
                if $size == 64    { $MVM_reg_num64 }
                elsif $size == 32 { $MVM_reg_num32 }
                else { nqp::die("Unknown num size $size") }
            }
            else {
                $MVM_reg_str
            }
        }
    }
}

# Shim that makes a compiler instance and uses it to drive compilation.
class QAST::MASTCompiler {
    method to_mast($qast) {
        MASTCompilerInstance.new.to_mast($qast)
    }

    method operations() {
        QAST::MASTOperations
    }

    method instance() {
        MASTCompilerInstance
    }
}

# Register as the QAST compiler.
if nqp::isnull(nqp::getcomp('QAST')) {
    nqp::bindcomp('QAST', QAST::MASTCompiler);
}

my %uint_map;
my %int_map;
my %num_map;
%int_map<8> := 1;
%int_map<16> := 2;
%int_map<32> := 3;
%int_map<64> := 4;
%num_map<32> := 5;
%num_map<64> := 6;
%uint_map<8> := 17;
%uint_map<16> := 18;
%uint_map<32> := 19;
%uint_map<64> := 20;
sub type_to_local_type($t) {
    my $spec := nqp::objprimspec($t);
    if $spec == 0 {
        8
    }
    elsif $spec == 1 {
        (nqp::objprimunsigned($t) ?? %uint_map !! %int_map){nqp::objprimbits($t)}
    }
    elsif $spec == 2 {
        %num_map{nqp::objprimbits($t)}
    }
    elsif $spec == 3 {
        7
    }
    else {
        nqp::die("Unknwon local type: " ~ $t.HOW.name($t) ~ ": " ~ $spec);
    }
}

class MoarVM::Callsites {
    has $!callsites;
    has %!callsites;
    has $!string-heap;
    has $!latin1decoder;
    method BUILD(:$string-heap) {
        $!string-heap   := $string-heap;
        $!callsites     := MAST::Bytecode.new;
        %!callsites     := nqp::hash;
        $!latin1decoder := NQPDecoder.new('iso-8859-1');
    }

    my $callsite_arg_named := 32;
    method get_callsite_id(@flags, @args) {
        my uint16 $elems := nqp::elems(@flags);
        my uint16 $align := $elems % 2;
        my @named_idxs := nqp::list;
        my int $num_nameds := 0;
        my int $i := 0;
        my $identifier := MAST::Bytecode.new;
        my $frame := $*MAST_FRAME;
        for @flags {
            if $_ +& $callsite_arg_named {
                my $name := @args[$i + $num_nameds++];
                nqp::push(@named_idxs, $frame.add-string($name));
                $identifier.write_uint32($_);
            }
            $identifier.write_uint8($_);
            $i++;
        }

        my $identifier_s := nqp::decode($identifier, 'iso-8859-1'); # just turn the buf into a str without real interpretation
        if nqp::existskey(%!callsites, $identifier_s) {
            return %!callsites{$identifier_s};
        }

        my $callsite-idx := nqp::elems(%!callsites);
        %!callsites{$identifier_s} := $callsite-idx;
        $!callsites.write_uint16($elems);
        for @flags {
            $!callsites.write_uint8($_);
        }
        if $align > 0 {
            $!callsites.write_uint8(0);
        }
        for @named_idxs {
            $!callsites.write_uint32($_);
        }
        $callsite-idx
    }

    my @kind_to_args := nqp::list_i;
    nqp::push_i(@kind_to_args, 0);
    nqp::push_i(@kind_to_args, $Arg::int);
    nqp::push_i(@kind_to_args, $Arg::int);
    nqp::push_i(@kind_to_args, $Arg::int);
    nqp::push_i(@kind_to_args, $Arg::int);
    nqp::push_i(@kind_to_args, $Arg::num);
    nqp::push_i(@kind_to_args, $Arg::num);
    nqp::push_i(@kind_to_args, $Arg::str);
    nqp::push_i(@kind_to_args, $Arg::obj);
    my int $flatnamed := $Arg::flatnamed;
    my int $flat      := $Arg::flat;
    my int $literal   := $Arg::literal;
    my int $named     := $Arg::named;
    method get_callsite_id_from_args(@args, @arg_mast) {
        my uint16 $elems := nqp::elems(@args);
        my @named_idxs := nqp::list_i;
        my int $i := 0;
        my $identifier := MAST::Bytecode.new;
        my uint64 $id_offset := 0;
        my $frame := $*MAST_FRAME;
        my @flags := nqp::list_i;
        for @args {
            my uint $result_typeflag := nqp::atpos_i(@kind_to_args, nqp::unbox_i(@arg_mast[$i].result_kind));
            if $_.flat {
                $result_typeflag := $result_typeflag +| ($_.named ?? $flatnamed !! $flat);
            }
            else {
                my str $name := $_.named;
                if $name {
                    my int $idx := nqp::unbox_i($frame.add-string($name));
                    nqp::push_i(@named_idxs, $idx);
                    nqp::writeuint($identifier, $id_offset, $idx, 9);
                    $id_offset := $id_offset + 4;
                    $result_typeflag := $result_typeflag +| $named;
                }
            }
            if nqp::istype($_, QAST::SVal) || nqp::istype($_, QAST::WVal) ||
                    nqp::istype($_, QAST::IVal) || nqp::istype($_, QAST::NVal) {
                $result_typeflag := $result_typeflag +| $literal;
            }
            nqp::push_i(@flags, $result_typeflag);

            nqp::writeuint($identifier, $id_offset++, $result_typeflag, 1);
            $i++;
        }

        $!latin1decoder.add-bytes($identifier); # just turn the buf into a str without real interpretation
        my str $identifier_s := $!latin1decoder.consume-all-chars;
        if nqp::existskey(%!callsites, $identifier_s) {
            return %!callsites{$identifier_s};
        }

        my $callsite-idx := nqp::elems(%!callsites);
        %!callsites{$identifier_s} := $callsite-idx;
        my uint $callsites_offset := nqp::elems($!callsites);
        nqp::writeuint($!callsites, $callsites_offset, $elems, 5);
        $callsites_offset := $callsites_offset + 2;
        my $iter := nqp::iterator(@flags);
        while $iter {
            nqp::writeuint($!callsites, $callsites_offset++, nqp::shift_i($iter), 1);
        }
        if $elems +& 1 {
            nqp::writeuint($!callsites, $callsites_offset++, 0, 1);
        }
        $iter := nqp::iterator(@named_idxs);
        while $iter {
            nqp::writeuint($!callsites, $callsites_offset, nqp::shift_i($iter), 9);
            $callsites_offset := $callsites_offset + 4;
        }
        $callsite-idx
    }

    method elems() {
        nqp::elems(%!callsites)
    }

    method size() {
        nqp::elems($!callsites)
    }

    method bytecode() {
        $!callsites
    }
}
$HLL::Backend::MoarVM::Callsites := MoarVM::Callsites; # circularity saw

class MoarVM::StringHeap {
    has $!strings;
    has uint $!strings-count;
    has @!orig-strings;
    has %!strings;
    method BUILD(:@strings) {
        $!strings := nqp::create(MAST::Bytecode);
        $!strings-count := 0;
        @!orig-strings := nqp::list_s();
        %!strings := nqp::hash();
        if nqp::islist(@strings) {
            for @strings {
                self.add($_ || '');
            }
        }
    }
    method add-internal(str $s) {
        my int $utf8 := 0;
        my int $i := 0;
        my int $chars := nqp::chars($s);
        while $i < $chars && !$utf8 {
            my int $g := nqp::getcp_s($s, $i++);
            $utf8 := 1 if $g < 0 || $g >= 0xff || $g == 0x0d;
        }

        my int $prev_total_size := nqp::elems($!strings);
        nqp::setelems($!strings, $prev_total_size + 4);
        nqp::encode($s, ($utf8 ?? "utf8" !! "iso-8859-1"), $!strings);
        my int $encoded_size := nqp::elems($!strings) - 4 - $prev_total_size;
        my int $pad := 4 - $encoded_size % 4;
        $pad := 0 if $pad == 4;

        $!strings.write_uint32_at($encoded_size * 2 + $utf8, $prev_total_size); # LSB is UTF-8 flag
        $!strings.write_uint8(0) while $pad--;

        nqp::push_s(@!orig-strings, $s);

        %!strings{$s} := $!strings-count++;
    }
    method add(str $s) {
        nqp::existskey(%!strings, $s) ?? %!strings{$s} !! self.add-internal($s)
    }
    method size() {
        my uint32 $size := nqp::elems($!strings);
        $size
    }
    method elems() {
        $!strings-count
    }
    method strings() {
        $!strings
    }
    method orig-strings() {
        @!orig-strings
    }
}
$HLL::Backend::MoarVM::StringHeap := MoarVM::StringHeap; # circularity saw

sub align_section($size) {
    my uint32 $aligned := nqp::mul_n(nqp::ceil_n(nqp::div_n($size, 8.0)), 8.0);
    $aligned
}
class MoarVM::BytecodeWriter {
    has $!mbc;
    has $!string-heap;
    has $!callsites;
    has $!annotations;
    has $!compunit;
    has @!frames;
    has $!bytecode;
    has uint32 $!bytecode_size;
    has @!sc_handle_idxs;
    has @!extop_name_idxs;
    has uint32 $!hll;
    method BUILD(:$string-heap, :$callsites, :$annotations) {
        $!mbc             := MAST::Bytecode.new;
        $!bytecode        := MAST::Bytecode.new;
        $!string-heap     := $string-heap;
        $!callsites       := $callsites;
        $!annotations     := $annotations;
        @!frames          := nqp::list;
        @!sc_handle_idxs  := nqp::list;
        @!extop_name_idxs := nqp::list;
    }
    method prepare() {
        self.collect_sc_deps;
        self.collect_extop_names;
        for @!frames {
            $_.prepare;
            $_.set-annotations-offset(nqp::elems($!annotations));
            $!annotations.write_buf($_.annotations);
        }
    }
    method set-compunit($compunit) { $!compunit := $compunit }
    method string-heap() { $!string-heap }
    method callsites()   { $!callsites }
    method annotations() { $!annotations }
    method add-string(str $s) {
        $!string-heap.add($s);
    }
    method add-frame(MAST::Frame $f) {
        nqp::push(@!frames, $f);
    }
    method write_header() {
        # 92 bytes

        my uint32 $header_size := +align_section(8 + 21 * 4);
        my uint32 $frames_size := 0;
        for @!frames {
            my uint32 $size := +$_.size;
            $frames_size := $frames_size + $size;
        }
        $frames_size := +align_section($frames_size);
        my uint32 $callsites_size := +align_section($!callsites.size);
        my uint32 $string_heap_size := +align_section($!string-heap.size);
        my @sc_handles := nqp::getattr($!compunit, MAST::CompUnit, '@!sc_handles');
        my uint32 $sc_deps_size := +align_section(nqp::elems(@sc_handles) * 4);
        my $num_extops := nqp::elems(nqp::getattr($!compunit, MAST::CompUnit, '@!extop_names'));
        my uint32 $extops_size := +align_section($num_extops * (4 + 8));
        my uint32 $bytecode_size := +align_section($!bytecode_size || nqp::elems($!bytecode));
        my uint32 $annotations_size := nqp::elems($!annotations); # doesn't need to be aligned because annotations are written last
        my $serialized := $!compunit.serialized;
        my uint32 $serialized_size := +align_section(nqp::defined($serialized) ?? nqp::elems($serialized) !! 0);

        my uint32 $offset := $header_size;
        $!mbc.write_s("MOARVM\r\n");
        $!mbc.write_uint32(7); # Version

        $!mbc.write_uint32($offset); # Offset of SC dependencies table
        $!mbc.write_uint32(nqp::elems(@sc_handles)); # Number of entries in SC dependencies table
        $offset := $offset + $sc_deps_size;

        $!mbc.write_uint32($offset); # Offset of extension ops table
        $!mbc.write_uint32($num_extops); # Number of entries in extension ops table
        $offset := $offset + $extops_size;

        $!mbc.write_uint32($offset); # Offset of frames segment
        $!mbc.write_uint32(nqp::elems(@!frames)); # Number of frames
        $offset := $offset + $frames_size;

        $!mbc.write_uint32($offset); # Offset of callsites segment
        $!mbc.write_uint32($!callsites.elems); # Number of callsites
        $offset := $offset + $callsites_size;

        $!mbc.write_uint32($offset); # Offset of strings heap
        $!mbc.write_uint32($!string-heap.elems); # Number of strings in heap
        $offset := $offset + $string_heap_size;

        $!mbc.write_uint32($offset); # Offset of SC data segment
        $!mbc.write_uint32($serialized_size); # Number of entries in SC data segment
        $offset := $offset + $serialized_size;

        $!mbc.write_uint32($offset); # Offset of bytecode segment
        $!mbc.write_uint32($!bytecode_size || nqp::elems($!bytecode)); # Length of bytecode segment
        $offset := $offset + $bytecode_size;

        $!mbc.write_uint32($offset); # Offset of annotation segment
        $!mbc.write_uint32($annotations_size); # Length of annotation segment

        $!mbc.write_uint32($!hll); # HLL Name
        my $mainline_frame := $!compunit.mainline_frame;
        if $mainline_frame {
            my uint32 $mainline_frame_idx := self.get_frame_index($mainline_frame) + 1;
            $!mbc.write_uint32($mainline_frame_idx); # Main entry point frame index + 1
        }
        else {
            $!mbc.write_uint32(0); # No mainline frame
        }
        my $main_frame := $!compunit.main_frame;
        if $main_frame {
            my uint32 $main_frame_idx := self.get_frame_index($main_frame) + 1;
            $!mbc.write_uint32($main_frame_idx); # Main entry point frame index + 1
        }
        else {
            $!mbc.write_uint32(0); # No main entry point frame
        }
        my $load_frame := $!compunit.load_frame;
        if $load_frame {
            my uint32 $load_frame_idx := self.get_frame_index($load_frame) + 1;
            $!mbc.write_uint32($load_frame_idx); # Library load frame index + 1
        }
        else {
            $!mbc.write_uint32(0); # No library load frame
        }
        my $deserialize_frame := $!compunit.deserialize_frame;
        if $deserialize_frame {
            my uint32 $deserialize_frame_idx := self.get_frame_index($deserialize_frame) + 1;
            $!mbc.write_uint32($deserialize_frame_idx); # Deserialization frame index + 1
        }
        else {
            $!mbc.write_uint32(0); # No deserialize frame
        }
    }
    method write_frame(MAST::Frame $f, int $idx) {
        # 12 * 4 + 3 * 2 = 54
        my @local_types := $f.local_types;
        my @lexical_types := $f.lexical_types;
        my @lexical_names := $f.lexical-name-idxs;
        my @static_lex_values := $f.static_lex_values;
        my uint16 $num_static_lex_values := nqp::elems(@static_lex_values) / 4;
        my @handlers := $f.handlers;
        my @debug_map_idxs := $f.debug_map_idxs;
        my int $debug_map_idxs_length := nqp::elems(@debug_map_idxs);
        $!mbc.write_uint32($f.bytecode-offset); # Bytecode segment offset
        $!mbc.write_uint32($f.bytecode-length); # Bytecode length in bytes
        $!mbc.write_uint32(nqp::elems(@local_types)); # Number of locals/registers
        $!mbc.write_uint32(nqp::elems(@lexical_types)); # Number of lexicals
        $!mbc.write_uint32($f.cuuid-idx); # Compilation unit unique ID (string heap index)
        $!mbc.write_uint32($f.name-idx); # Name (string heap index)
        my $outer := $f.outer;
        if nqp::defined($outer) {
            $!mbc.write_uint16(self.get_frame_index($outer)); # Outer
        }
        else {
            $!mbc.write_uint16($idx); # Outer
        }
        $!mbc.write_uint32($f.annotations-offset); # Annotation segment offset
        $!mbc.write_uint32($f.num-annotations); # Number of annotations
        $!mbc.write_uint32(nqp::elems(@handlers)); # Number of handlers
        $!mbc.write_uint16($f.flags); # Frame flag bits
        $!mbc.write_uint16($num_static_lex_values); # Number of entries in static lexical values table
        if $f.flags +& 4 { # FRAME_FLAG_HAS_CODE_OBJ
            $!mbc.write_uint32(nqp::add_i($f.code_obj_sc_dep_idx, 1)); # Code object SC dependency index + 1
            $!mbc.write_uint32($f.code_obj_sc_idx); # SC object index
        }
        else {
            $!mbc.write_uint32(0); # No code object SC dependency index
            $!mbc.write_uint32(0); # No SC object index
        }
        $!mbc.write_uint32(nqp::elems($f.debug_map));
        for @local_types {
            $!mbc.write_uint16(type_to_local_type($_));
        }
        my int $i := 0;
        for @lexical_types {
            $!mbc.write_uint16(type_to_local_type($_));
            $!mbc.write_uint32(nqp::atpos_i(@lexical_names, $i++));
        }
        for @handlers {
            $!mbc.write_uint32($_.start_offset);
            $!mbc.write_uint32($_.end_offset);
            $!mbc.write_uint32($_.category_mask);
            $!mbc.write_uint16($_.action);
            $!mbc.write_uint16($_.local);
            $!mbc.write_uint32($f.resolve-label($_.label));
            if $_.category_mask +& 4096 { # MVM_EX_CATEGORY_LABELED
                $!mbc.write_uint16($_.label_reg);
            }
        }
        $i := 0;
        while ($i < $num_static_lex_values) {
            $!mbc.write_uint16(nqp::atpos_i(@static_lex_values, 4 * $i));
            $!mbc.write_uint16(nqp::atpos_i(@static_lex_values, 4 * $i + 1));
            $!mbc.write_uint32(nqp::atpos_i(@static_lex_values, 4 * $i + 2));
            $!mbc.write_uint32(nqp::atpos_i(@static_lex_values, 4 * $i + 3));
            $i++;
        }
        $i := 0;
        while $i < $debug_map_idxs_length {
            $!mbc.write_uint16(nqp::atpos_i(@debug_map_idxs, $i++));
            $!mbc.write_uint32(nqp::atpos_i(@debug_map_idxs, $i++));
        }
    }
    method collect_bytecode() {
        for @!frames {
            $_.set-bytecode-offset(nqp::elems($!bytecode));
            $!bytecode.write_buf($_.bytecode);
        }
    }
    method write_callsites() {
        $!mbc.write_buf($!callsites.bytecode);
    }
    method write_string_heap() {
        $!mbc.write_buf($!string-heap.strings);
    }
    method write_serialized_data() {
        $!mbc.write_buf($!compunit.serialized) if nqp::defined($!compunit.serialized);
    }
    method collect_sc_deps() {
        my @sc_handles := nqp::getattr($!compunit, MAST::CompUnit, '@!sc_handles');
        for @sc_handles {
            nqp::push(@!sc_handle_idxs, self.add-string($_));
        }
    }
    method collect_extop_names() {
        my @extop_names := nqp::getattr($!compunit, MAST::CompUnit, '@!extop_names');
        for @extop_names {
            nqp::push(@!extop_name_idxs, self.add-string($_));
        }
    }
    method write_sc_deps_table() {
        for @!sc_handle_idxs {
            $!mbc.write_uint32($_);
        }
    }
    method write_extops() {
        my $num_extops := nqp::elems(nqp::getattr($!compunit, MAST::CompUnit, '@!extop_names'));
        my @extop_sigs := nqp::getattr($!compunit, MAST::CompUnit, '@!extop_sigs');
        my $i := 0;
        while $i < $num_extops {
            $!mbc.write_uint32(@!extop_name_idxs[$i]);
            my @sig_array := @extop_sigs[$i];
            my $num_operands := nqp::elems(@sig_array);
            my $j := 0;
            while $j < 8 {
                $!mbc.write_uint8($j < $num_operands ?? nqp::atpos_i(@sig_array, $j) !! 0);
                $j++;
            }
            $i++;
        }
    }
    method write_annotations() {
        $!mbc.write_buf($!annotations);
    }
    method align() {
        my $off := nqp::elems($!mbc) % 8;
        if $off == 0 {
            return;
        }
        $off := 8 - $off;
        while $off-- > 0 {
            $!mbc.write_uint8(0);
        }
    }
    method align_and_write($file) {
        self.align;
        nqp::writefh($file, $!mbc);
        nqp::setelems($!mbc, 0);
    }
    method align_file($size, $file) {
        my $off := $size % 8;
        if $off != 0 {
            my $tmp := MAST::Bytecode.new;
            $off := 8 - $off;
            while $off-- > 0 {
                $tmp.write_uint8(0);
            }
            nqp::writefh($file, $tmp);
        }
    }

    method assemble() {
        $!hll := self.add-string($!compunit.hll || '');
        self.collect_bytecode;

        self.write_header;
        self.align;
        self.write_sc_deps_table;
        self.align;
        self.write_extops;
        self.align;
        my int $idx := 0;
        for @!frames {
            self.write_frame($_, $idx++);
        }
        self.align;
        self.write_callsites;
        self.align;
        self.write_string_heap;
        self.align;
        self.write_serialized_data;
        self.align;
        $!mbc.write_buf($!bytecode);
        self.align;
        self.write_annotations;
        self.align;
    }
    method assemble_to_file($filename) {
        $!hll := self.add-string($!compunit.hll || '');
        my $file := nqp::open($filename, 'w');

        # skip the header since we don't have all the info yet, we'll go back and write it later
        nqp::seekfh($file, 96, 0);

        self.write_sc_deps_table;
        self.align_and_write($file);
        self.write_extops;
        self.align_and_write($file);
        my int $idx := 0;
        for @!frames {
            # need to set the bycode offset here since we don't call self.collect_bytecode()
            $_.set-bytecode-offset($!bytecode_size);
            self.write_frame($_, $idx++);
            $!bytecode_size := $!bytecode_size + nqp::elems($_.bytecode);
        }
        self.align_and_write($file);
        self.write_callsites;
        self.align_and_write($file);
        self.write_string_heap;
        self.align_and_write($file);

        # write the compunit serialized data directly to the file since it's large
        if nqp::defined($!compunit.serialized) {
            my int $compunit_size := nqp::writefh($file, $!compunit.serialized);
            self.align_file($compunit_size, $file);
        }

        # write the bytecode directly to the file since it's large
        for @!frames {
            nqp::writefh($file, $_.bytecode);
        }
        self.align_file($!bytecode_size, $file);

        self.write_annotations;
        self.align_and_write($file);

        # go back to the front of the file and write the header
        nqp::seekfh($file, 0, 0);
        self.write_header;
        self.align_and_write($file);

        nqp::closefh($file);
    }
    method get_frame_index(MAST::Frame $f) {
        my $idx := 0;
        if nqp::getattr($f, MAST::Frame, '$!flags') +& 32768 { # FRAME_FLAG_HAS_INDEX
            return nqp::getattr($f, MAST::Frame, '$!frame_idx');
        }
        for nqp::getattr($!compunit, MAST::CompUnit, '@!frames') {
            return $idx if nqp::objectid($_) eq nqp::objectid($f);
            $idx++;
        }
        nqp::die("Could not find frame " ~ $f.name);
    }
    method save($filename) {
        my $io := nqp::open($filename, 'w');
        nqp::writefh($io, $!mbc);
        nqp::closefh($io);
    }
    method bytecode() {
        $!mbc
    }
}

class MASTBytecodeAssembler {
    method assemble_to_file($mast, $filename) {
        my $writer := $mast.writer;
        my @cu_frames := nqp::getattr($mast, MAST::CompUnit, '@!frames');
        for @cu_frames {
            $writer.add-frame($_);
        }
        $writer.prepare;
        $writer.assemble_to_file($filename);
    }

    method assemble($mast) {
        my $writer := $mast.writer;
        my @cu_frames := nqp::getattr($mast, MAST::CompUnit, '@!frames');
        for @cu_frames {
            $writer.add-frame($_);
        }
        $writer.prepare;
        $writer.assemble;
        $writer
    }

    method assemble_and_load($mast) {
        nqp::buffertocu(self.assemble($mast).bytecode);
    }
}

if nqp::isnull(nqp::getcomp('MAST')) {
    nqp::bindcomp('MAST', MASTBytecodeAssembler);
}
