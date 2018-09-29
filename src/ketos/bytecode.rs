//! Implements encoding and decoding of bytecode instruction format.
//!
//! Bytecode instructions consist of a one-byte operand, followed by zero or more
//! unsigned integer operands in the range `[0, 0x7fff]` (15 bits).
//!
//! Operands in the range `[0, 0x7f]` are encoded as a single byte. Operands in
//! the range `[0x80, 0x7fff]` are encoded as two bytes: the first containing
//! the higher 7 bits of the operand with the 8th bit set; the second containing
//! the lower 8 bits of the operand.
//!
//! Combination instructions exist to combine the operation of two or more
//! instructions which commonly follow, e.g. `ConstPush(n)` operates as
//! `Const(n)` followed by `Push`.
//!
//! Shortcut opcodes exist for common instructions that accept operands,
//! such as `Const` and `Load`. These opcodes replace a long-form instruction
//! with a single opcode, e.g. the `CONST_0` opcode replaces the two-byte
//! sequence `CONST`, followed by operand `0`.

use compile::CompileError;
use exec::ExecError;
use function::Arity;
use name::Name;
use value::Value;

/// Bytecode version number, indicating the version of the most recent breaking
/// change to the bytecode format. The version represents a `ketos` version
/// number, e.g. `0x01_02_03_00` corresponds to version `1.2.3`.
/// (The least significant 8 bits don't mean anything yet.)
pub const BYTECODE_VERSION: u32 = 0x00_0b_00_00;

/// Maximum value of a short-encoded operand.
pub const MAX_SHORT_OPERAND: u32 = 0x7f;

/// Maximum value of a long-encoded operand.
pub const MAX_LONG_OPERAND: u32 = 0x7fff;

/// Represents an instruction and any immediate parameters.
///
/// Any addition, deletion, or modification to this enum constitutes
/// a breaking change to the bytecode format.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Instruction {
    /// Load a value from the stack
    Load(u32),
    /// Load a value from enclosed values
    LoadC(u32),
    /// If value *n* on the stack is `Unbound`, replace it with `()`.
    UnboundToUnit(u32),
    /// Load a named value from global scope
    GetDef(u32),
    /// Push a value onto the stack; value is invalidated.
    Push,
    /// Load `()` into value
    Unit,
    /// Load `true` into value
    True,
    /// Load `false` into value
    False,
    /// Load a const into value
    Const(u32),
    /// Store a value in the stack; value is invalidated.
    Store(u32),
    /// Load, then push
    LoadPush(u32),
    /// Load enclosed value, then push
    LoadCPush(u32),
    /// Load a name from global scope, then push
    GetDefPush(u32),
    /// Load `()`, then push
    UnitPush,
    /// Load `true`, then push
    TruePush,
    /// Load `false`, then push
    FalsePush,
    /// Load a const, then push
    ConstPush(u32),
    /// Assign a value to a name into global scope
    SetDef(u32),
    /// Build a list of *n* values from the stack
    List(u32),
    /// Transform value into an *n*-quoted value
    Quote(u32),
    /// Transform value into an *n*-quasiquoted value
    Quasiquote(u32),
    /// Transform value into an *n*-comma'd value
    Comma(u32),
    /// Transform value into an *n*-comma-at'd value
    CommaAt(u32),
    /// Create a closure from code object in *n_const* and a list of
    /// *n_values* values on the stack; parameters are `(n_const, n_values)`.
    BuildClosure(u32, u32),
    /// Jump to a label
    Jump(u32),
    /// Jump if value is `true`
    JumpIf(u32),
    /// Jump if value *n* from the stack is bound; parameters are `(label, n)`
    JumpIfBound(u32, u32),
    /// Jump if value is `false`
    JumpIfNot(u32),
    /// Jump if value is `()`
    JumpIfNull(u32),
    /// Jump if value is not `()`
    JumpIfNotNull(u32),
    /// Jump if value is equal to top of stack
    JumpIfEq(u32),
    /// Jump if value is not equal to top of stack
    JumpIfNotEq(u32),
    /// Jump if value is equal to const; parameters are `(label, n)`
    JumpIfEqConst(u32, u32),
    /// Jump if value is not equal to const; parameters are `(label, n)`
    JumpIfNotEqConst(u32, u32),
    /// Test whether value is `()`
    Null,
    /// Test whether value is not `()`
    NotNull,
    /// Pops from the top of the stack and tests for equality with value.
    Eq,
    /// Pops from the top of the stack and tesst for inequality with value.
    NotEq,
    /// Tests value for equality with const *n*
    EqConst(u32),
    /// Tests value for inequality with const *n*
    NotEqConst(u32),
    /// Negate boolean value
    Not,
    /// Increment integer value
    Inc,
    /// Decrement integer value
    Dec,
    /// Append value to list on top of stack; result will be in value
    Append,
    /// Take first element of list or string and assign to value
    First,
    /// Take tail of list or string and assign to value
    Tail,
    /// Take head of list or string and assign to value
    Init,
    /// Take last element of list or string and assign to value
    Last,
    /// Push first value from list or string
    FirstPush,
    /// Push tail from list or string
    TailPush,
    /// Push head from list or string
    InitPush,
    /// Push last value from list or string
    LastPush,
    /// Call system function *n* with known number of arguments on stack.
    /// Only functions with `Exact` arity may be called in this manner.
    CallSys(u32),
    /// Call system function with *n* arguments on the stack;
    /// parameters are `(sys_fn, n_args)`.
    CallSysArgs(u32, u32),
    /// Call const function with arguments on the stack;
    /// parameters are `(const, n_args)`.
    CallConst(u32, u32),
    /// Call function on the stack with *n* arguments from the top of the stack
    Call(u32),
    /// Call function on the stack with *n* stack arguments,
    /// plus additional arguments from list value
    Apply(u32),
    /// Call const function with *n* stack arguments,
    /// plus additional arguments from list value;
    /// parameters are `(const, n_args)`.
    ApplyConst(u32, u32),
    /// Call current code object with *n* stack arguments,
    /// plus additional arguments from list value;
    /// does not perform a tail call
    ApplySelf(u32),
    /// Call current code object with *n* stack arguments,
    /// plus additional arguments from list value
    TailApplySelf(u32),
    /// Call current code object with *n* arguments from the top of the stack;
    /// this does not perform a tail call
    CallSelf(u32),
    /// Perform tail-recursive call with *n* arguments from the top of the stack
    TailCallSelf(u32),
    /// Remove *n* values from the top of the stack
    Skip(u32),
    /// Return value from function
    Return,
}

macro_rules! opcodes {
    ( $( $name:ident = $value:expr , )+ ) => {
        /// Opcode values of compiled bytecode.
        ///
        /// Any addition, deletion, or modification to these constants constitutes
        /// a breaking change to the bytecode format.
        #[allow(missing_docs)]
        pub mod opcodes {
            $( pub const $name: u8 = $value; )+
        }
    }
}

opcodes!{
    LOAD = 0,
    LOAD_0 = 1,
    LOAD_1 = 2,
    LOAD_2 = 3,
    LOAD_3 = 4,
    LOADC = 5,
    LOADC_0 = 6,
    LOADC_1 = 7,
    LOADC_2 = 8,
    LOADC_3 = 9,
    UNBOUND_TO_UNIT = 10,
    UNBOUND_TO_UNIT_0 = 11,
    UNBOUND_TO_UNIT_1 = 12,
    UNBOUND_TO_UNIT_2 = 13,
    UNBOUND_TO_UNIT_3 = 14,
    GET_DEF = 15,
    GET_DEF_0 = 16,
    GET_DEF_1 = 17,
    GET_DEF_2 = 18,
    GET_DEF_3 = 19,
    PUSH = 20,
    UNIT = 21,
    TRUE = 22,
    FALSE = 23,
    CONST = 24,
    CONST_0 = 25,
    CONST_1 = 26,
    CONST_2 = 27,
    CONST_3 = 28,
    CONST_4 = 29,
    CONST_5 = 30,
    CONST_6 = 31,
    CONST_7 = 32,
    STORE = 33,
    STORE_0 = 34,
    STORE_1 = 35,
    STORE_2 = 36,
    STORE_3 = 37,
    LOAD_PUSH = 38,
    LOAD_PUSH_0 = 39,
    LOAD_PUSH_1 = 40,
    LOAD_PUSH_2 = 41,
    LOAD_PUSH_3 = 42,
    LOADC_PUSH = 43,
    LOADC_PUSH_0 = 44,
    LOADC_PUSH_1 = 45,
    LOADC_PUSH_2 = 46,
    LOADC_PUSH_3 = 47,
    GET_DEF_PUSH = 48,
    UNIT_PUSH = 49,
    TRUE_PUSH = 50,
    FALSE_PUSH = 51,
    CONST_PUSH = 52,
    CONST_PUSH_0 = 53,
    CONST_PUSH_1 = 54,
    CONST_PUSH_2 = 55,
    CONST_PUSH_3 = 56,
    CONST_PUSH_4 = 57,
    CONST_PUSH_5 = 58,
    CONST_PUSH_6 = 59,
    CONST_PUSH_7 = 60,
    SET_DEF = 61,
    LIST = 62,
    QUOTE = 63,
    QUOTE_1 = 64,
    QUASIQUOTE = 65,
    QUASIQUOTE_1 = 66,
    COMMA = 67,
    COMMA_1 = 68,
    COMMA_AT = 69,
    COMMA_AT_1 = 70,
    BUILD_CLOSURE = 71,
    JUMP = 72,
    JUMP_IF = 73,
    JUMP_IF_BOUND = 74,
    JUMP_IF_NOT = 75,
    JUMP_IF_NULL = 76,
    JUMP_IF_NOT_NULL = 77,
    JUMP_IF_EQ = 78,
    JUMP_IF_NOT_EQ = 79,
    JUMP_IF_EQ_CONST = 80,
    JUMP_IF_NOT_EQ_CONST = 81,
    NULL = 82,
    NOT_NULL = 83,
    EQ = 84,
    NOT_EQ = 85,
    EQ_CONST = 86,
    NOT_EQ_CONST = 87,
    NOT = 88,
    INC = 89,
    DEC = 90,
    APPEND = 91,
    FIRST = 92,
    TAIL = 93,
    INIT = 94,
    LAST = 95,
    FIRST_PUSH = 96,
    TAIL_PUSH = 97,
    INIT_PUSH = 98,
    LAST_PUSH = 99,
    CALL_SYS = 100,
    CALL_SYS_ARGS = 101,
    CALL_CONST = 102,
    CALL_CONST_0 = 103,
    CALL_CONST_1 = 104,
    CALL_CONST_2 = 105,
    CALL_CONST_3 = 106,
    CALL_CONST_4 = 107,
    CALL_CONST_5 = 108,
    CALL_CONST_6 = 109,
    CALL_CONST_7 = 110,
    CALL = 111,
    APPLY = 112,
    APPLY_CONST = 113,
    APPLY_SELF = 114,
    TAIL_APPLY_SELF = 115,
    CALL_SELF = 116,
    TAIL_CALL_SELF = 117,
    SKIP = 118,
    SKIP_1 = 119,
    SKIP_2 = 120,
    SKIP_3 = 121,
    SKIP_4 = 122,
    RETURN = 123,
}

impl Instruction {
    /// Decodes a single `Instruction` from a `CodeReader`.
    pub fn decode(r: &mut CodeReader) -> Result<Instruction, ExecError> {
        use self::opcodes::*;
        use self::Instruction::*;

        macro_rules! operand {
            () => { r.read_operand()? }
        }

        let op = r.read_byte()?;

        let instr = match op {
            LOAD => Load(operand!()),
            LOAD_0 => Load(0),
            LOAD_1 => Load(1),
            LOAD_2 => Load(2),
            LOAD_3 => Load(3),
            LOADC => LoadC(operand!()),
            LOADC_0 => LoadC(0),
            LOADC_1 => LoadC(1),
            LOADC_2 => LoadC(2),
            LOADC_3 => LoadC(3),
            UNBOUND_TO_UNIT => UnboundToUnit(operand!()),
            UNBOUND_TO_UNIT_0 => UnboundToUnit(0),
            UNBOUND_TO_UNIT_1 => UnboundToUnit(1),
            UNBOUND_TO_UNIT_2 => UnboundToUnit(2),
            UNBOUND_TO_UNIT_3 => UnboundToUnit(3),
            GET_DEF => GetDef(operand!()),
            GET_DEF_0 => GetDef(0),
            GET_DEF_1 => GetDef(1),
            GET_DEF_2 => GetDef(2),
            GET_DEF_3 => GetDef(3),
            PUSH => Push,
            UNIT => Unit,
            TRUE => True,
            FALSE => False,
            CONST => Const(operand!()),
            CONST_0 => Const(0),
            CONST_1 => Const(1),
            CONST_2 => Const(2),
            CONST_3 => Const(3),
            CONST_4 => Const(4),
            CONST_5 => Const(5),
            CONST_6 => Const(6),
            CONST_7 => Const(7),
            STORE => Store(operand!()),
            STORE_0 => Store(0),
            STORE_1 => Store(1),
            STORE_2 => Store(2),
            STORE_3 => Store(3),
            LOAD_PUSH => LoadPush(operand!()),
            LOAD_PUSH_0 => LoadPush(0),
            LOAD_PUSH_1 => LoadPush(1),
            LOAD_PUSH_2 => LoadPush(2),
            LOAD_PUSH_3 => LoadPush(3),
            LOADC_PUSH => LoadCPush(operand!()),
            LOADC_PUSH_0 => LoadCPush(0),
            LOADC_PUSH_1 => LoadCPush(1),
            LOADC_PUSH_2 => LoadCPush(2),
            LOADC_PUSH_3 => LoadCPush(3),
            GET_DEF_PUSH => GetDefPush(operand!()),
            UNIT_PUSH => UnitPush,
            TRUE_PUSH => TruePush,
            FALSE_PUSH => FalsePush,
            CONST_PUSH => ConstPush(operand!()),
            CONST_PUSH_0 => ConstPush(0),
            CONST_PUSH_1 => ConstPush(1),
            CONST_PUSH_2 => ConstPush(2),
            CONST_PUSH_3 => ConstPush(3),
            CONST_PUSH_4 => ConstPush(4),
            CONST_PUSH_5 => ConstPush(5),
            CONST_PUSH_6 => ConstPush(6),
            CONST_PUSH_7 => ConstPush(7),
            SET_DEF => SetDef(operand!()),
            LIST => List(operand!()),
            QUOTE => Quote(operand!()),
            QUOTE_1 => Quote(1),
            QUASIQUOTE => Quasiquote(operand!()),
            QUASIQUOTE_1 => Quasiquote(1),
            COMMA => Comma(operand!()),
            COMMA_1 => Comma(1),
            COMMA_AT => CommaAt(operand!()),
            COMMA_AT_1 => CommaAt(1),
            BUILD_CLOSURE => BuildClosure(operand!(), operand!()),
            JUMP => Jump(operand!()),
            JUMP_IF => JumpIf(operand!()),
            JUMP_IF_BOUND => JumpIfBound(operand!(), operand!()),
            JUMP_IF_NOT => JumpIfNot(operand!()),
            JUMP_IF_NULL => JumpIfNull(operand!()),
            JUMP_IF_NOT_NULL => JumpIfNotNull(operand!()),
            JUMP_IF_EQ => JumpIfEq(operand!()),
            JUMP_IF_NOT_EQ => JumpIfNotEq(operand!()),
            JUMP_IF_EQ_CONST => JumpIfEqConst(operand!(), operand!()),
            JUMP_IF_NOT_EQ_CONST => JumpIfNotEqConst(operand!(), operand!()),
            NULL => Null,
            NOT_NULL => NotNull,
            EQ => Eq,
            NOT_EQ => NotEq,
            EQ_CONST => EqConst(operand!()),
            NOT_EQ_CONST => NotEqConst(operand!()),
            NOT => Not,
            INC => Inc,
            DEC => Dec,
            APPEND => Append,
            FIRST => First,
            TAIL => Tail,
            INIT => Init,
            LAST => Last,
            FIRST_PUSH => FirstPush,
            TAIL_PUSH => TailPush,
            INIT_PUSH => InitPush,
            LAST_PUSH => LastPush,
            CALL_SYS => CallSys(operand!()),
            CALL_SYS_ARGS => CallSysArgs(operand!(), operand!()),
            CALL_CONST => CallConst(operand!(), operand!()),
            CALL_CONST_0 => CallConst(0, operand!()),
            CALL_CONST_1 => CallConst(1, operand!()),
            CALL_CONST_2 => CallConst(2, operand!()),
            CALL_CONST_3 => CallConst(3, operand!()),
            CALL_CONST_4 => CallConst(4, operand!()),
            CALL_CONST_5 => CallConst(5, operand!()),
            CALL_CONST_6 => CallConst(6, operand!()),
            CALL_CONST_7 => CallConst(7, operand!()),
            CALL => Call(operand!()),
            APPLY => Apply(operand!()),
            APPLY_CONST => ApplyConst(operand!(), operand!()),
            APPLY_SELF => ApplySelf(operand!()),
            TAIL_APPLY_SELF => TailApplySelf(operand!()),
            CALL_SELF => CallSelf(operand!()),
            TAIL_CALL_SELF => TailCallSelf(operand!()),
            SKIP => Skip(operand!()),
            SKIP_1 => Skip(1),
            SKIP_2 => Skip(2),
            SKIP_3 => Skip(3),
            SKIP_4 => Skip(4),
            RETURN => Return,
            _ => return Err(ExecError::UnrecognizedOpCode(op))
        };

        Ok(instr)
    }

    /// Encodes a single `Instruction` into a `CodeBlock`.
    pub fn encode(&self, w: &mut CodeBlock, short: bool) -> Result<(), CompileError> {
        use self::opcodes::*;
        use self::Instruction::*;

        // Writes opcodes and operands
        macro_rules! op {
            ( $opcode:expr ) => {
                w.write_byte($opcode)
            };
            ( $opcode:expr , $( $opr:expr ),+ ) => {
                w.write_byte($opcode)
                    $( .and_then(|_| w.write_operand($opr)) )+
            }
        }

        // Writes jump instructions and operands; label always comes first.
        macro_rules! jump_op {
            ( $opcode:expr, $label:expr ) => {
                w.write_byte($opcode)
                    .and_then(|_| w.write_label_operand($label, short))
            };
            ( $opcode:expr, $label:expr , $( $opr:expr ),+ ) => {
                w.write_byte($opcode)
                    .and_then(|_| w.write_label_operand($label, short))
                    $( .and_then(|_| w.write_operand($opr)) )+
            }
        }

        match *self {
            Load(0) => op!(LOAD_0),
            Load(1) => op!(LOAD_1),
            Load(2) => op!(LOAD_2),
            Load(3) => op!(LOAD_3),
            Load(n) => op!(LOAD, n),
            LoadC(0) => op!(LOADC_0),
            LoadC(1) => op!(LOADC_1),
            LoadC(2) => op!(LOADC_2),
            LoadC(3) => op!(LOADC_3),
            LoadC(n) => op!(LOADC, n),
            UnboundToUnit(0) => op!(UNBOUND_TO_UNIT_0),
            UnboundToUnit(1) => op!(UNBOUND_TO_UNIT_1),
            UnboundToUnit(2) => op!(UNBOUND_TO_UNIT_2),
            UnboundToUnit(3) => op!(UNBOUND_TO_UNIT_3),
            UnboundToUnit(n) => op!(UNBOUND_TO_UNIT, n),
            GetDef(0) => op!(GET_DEF_0),
            GetDef(1) => op!(GET_DEF_1),
            GetDef(2) => op!(GET_DEF_2),
            GetDef(3) => op!(GET_DEF_3),
            GetDef(n) => op!(GET_DEF, n),
            Push => op!(PUSH),
            Unit => op!(UNIT),
            True => op!(TRUE),
            False => op!(FALSE),
            Const(0) => op!(CONST_0),
            Const(1) => op!(CONST_1),
            Const(2) => op!(CONST_2),
            Const(3) => op!(CONST_3),
            Const(4) => op!(CONST_4),
            Const(5) => op!(CONST_5),
            Const(6) => op!(CONST_6),
            Const(7) => op!(CONST_7),
            Const(n) => op!(CONST, n),
            Store(0) => op!(STORE_0),
            Store(1) => op!(STORE_1),
            Store(2) => op!(STORE_2),
            Store(3) => op!(STORE_3),
            Store(n) => op!(STORE, n),
            LoadPush(0) => op!(LOAD_PUSH_0),
            LoadPush(1) => op!(LOAD_PUSH_1),
            LoadPush(2) => op!(LOAD_PUSH_2),
            LoadPush(3) => op!(LOAD_PUSH_3),
            LoadPush(n) => op!(LOAD_PUSH, n),
            LoadCPush(0) => op!(LOADC_PUSH_0),
            LoadCPush(1) => op!(LOADC_PUSH_1),
            LoadCPush(2) => op!(LOADC_PUSH_2),
            LoadCPush(3) => op!(LOADC_PUSH_3),
            LoadCPush(n) => op!(LOADC_PUSH, n),
            GetDefPush(n) => op!(GET_DEF_PUSH, n),
            UnitPush => op!(UNIT_PUSH),
            TruePush => op!(TRUE_PUSH),
            FalsePush => op!(FALSE_PUSH),
            ConstPush(0) => op!(CONST_PUSH_0),
            ConstPush(1) => op!(CONST_PUSH_1),
            ConstPush(2) => op!(CONST_PUSH_2),
            ConstPush(3) => op!(CONST_PUSH_3),
            ConstPush(4) => op!(CONST_PUSH_4),
            ConstPush(5) => op!(CONST_PUSH_5),
            ConstPush(6) => op!(CONST_PUSH_6),
            ConstPush(7) => op!(CONST_PUSH_7),
            ConstPush(n) => op!(CONST_PUSH, n),
            SetDef(n) => op!(SET_DEF, n),
            List(n) => op!(LIST, n),
            Quote(1) => op!(QUOTE_1),
            Quote(n) => op!(QUOTE, n),
            Quasiquote(1) => op!(QUASIQUOTE_1),
            Quasiquote(n) => op!(QUASIQUOTE, n),
            Comma(1) => op!(COMMA_1),
            Comma(n) => op!(COMMA, n),
            CommaAt(1) => op!(COMMA_AT_1),
            CommaAt(n) => op!(COMMA_AT, n),
            BuildClosure(n_const, n_values) => op!(BUILD_CLOSURE, n_const, n_values),
            Jump(label) => jump_op!(JUMP, label),
            JumpIf(label) => jump_op!(JUMP_IF, label),
            JumpIfBound(label, n) => jump_op!(JUMP_IF_BOUND, label, n),
            JumpIfNot(label) => jump_op!(JUMP_IF_NOT, label),
            JumpIfNull(label) => jump_op!(JUMP_IF_NULL, label),
            JumpIfNotNull(label) => jump_op!(JUMP_IF_NOT_NULL, label),
            JumpIfEq(label) => jump_op!(JUMP_IF_EQ, label),
            JumpIfNotEq(label) => jump_op!(JUMP_IF_NOT_EQ, label),
            JumpIfEqConst(label, n) => jump_op!(JUMP_IF_EQ_CONST, label, n),
            JumpIfNotEqConst(label, n) => jump_op!(JUMP_IF_NOT_EQ_CONST, label, n),
            Null => op!(NULL),
            NotNull => op!(NOT_NULL),
            Eq => op!(EQ),
            NotEq => op!(NOT_EQ),
            EqConst(n) => op!(EQ_CONST, n),
            NotEqConst(n) => op!(NOT_EQ_CONST, n),
            Not => op!(NOT),
            Inc => op!(INC),
            Dec => op!(DEC),
            Append => op!(APPEND),
            First => op!(FIRST),
            Tail => op!(TAIL),
            Init => op!(INIT),
            Last => op!(LAST),
            FirstPush => op!(FIRST_PUSH),
            TailPush => op!(TAIL_PUSH),
            InitPush => op!(INIT_PUSH),
            LastPush => op!(LAST_PUSH),
            CallSys(n) => op!(CALL_SYS, n),
            CallSysArgs(n_args, n_rest) => op!(CALL_SYS_ARGS, n_args, n_rest),
            CallConst(0, n_args) => op!(CALL_CONST_0, n_args),
            CallConst(1, n_args) => op!(CALL_CONST_1, n_args),
            CallConst(2, n_args) => op!(CALL_CONST_2, n_args),
            CallConst(3, n_args) => op!(CALL_CONST_3, n_args),
            CallConst(4, n_args) => op!(CALL_CONST_4, n_args),
            CallConst(5, n_args) => op!(CALL_CONST_5, n_args),
            CallConst(6, n_args) => op!(CALL_CONST_6, n_args),
            CallConst(7, n_args) => op!(CALL_CONST_7, n_args),
            CallConst(n, n_args) => op!(CALL_CONST, n, n_args),
            Call(n) => op!(CALL, n),
            Apply(n) => op!(APPLY, n),
            ApplyConst(n, n_args) => op!(APPLY_CONST, n, n_args),
            ApplySelf(n) => op!(APPLY_SELF, n),
            TailApplySelf(n) => op!(TAIL_APPLY_SELF, n),
            CallSelf(n) => op!(CALL_SELF, n),
            TailCallSelf(n) => op!(TAIL_CALL_SELF, n),
            Skip(1) => op!(SKIP_1),
            Skip(2) => op!(SKIP_2),
            Skip(3) => op!(SKIP_3),
            Skip(4) => op!(SKIP_4),
            Skip(n) => op!(SKIP, n),
            Return => op!(RETURN),
        }
    }

    /// Returns whether the `Instruction` is trivial;
    /// that is, in valid top-level code, it does not produce any side effects.
    pub fn is_trivial(&self) -> bool {
        use self::Instruction::*;

        match *self {
            Unit | True | False | Const(_) | Return => true,
            _ => false
        }
    }

    /// If the instruction is a jump instruction, returns the jump offset.
    /// Otherwise, returns `None`.
    pub fn jump_label(&self) -> Option<u32> {
        use self::Instruction::*;

        match *self {
            Jump(label) |
            JumpIf(label) |
            JumpIfBound(label, _) |
            JumpIfNot(label) |
            JumpIfNull(label) |
            JumpIfNotNull(label) |
            JumpIfEq(label) |
            JumpIfNotEq(label) |
            JumpIfEqConst(label, _) |
            JumpIfNotEqConst(label, _) => Some(label),
            _ => None
        }
    }

    /// Returns the maximum length, in bytes, of an encoded instruction.
    pub fn max_len() -> usize { 5 }
}

/// Partial representation of jump `Instruction` variants before label values
/// have been determined.
#[allow(missing_docs)]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum JumpInstruction {
    Jump,
    JumpIf,
    JumpIfBound(u32),
    JumpIfNot,
    JumpIfNull,
    JumpIfNotNull,
    JumpIfEq,
    JumpIfNotEq,
    JumpIfEqConst(u32),
    JumpIfNotEqConst(u32),
}

impl JumpInstruction {
    /// Returns an `Instruction` by inserting the given label value.
    pub fn set_label(self, label: u32) -> Instruction {
        use self::JumpInstruction::*;

        match self {
            Jump => Instruction::Jump(label),
            JumpIf => Instruction::JumpIf(label),
            JumpIfBound(n) => Instruction::JumpIfBound(label, n),
            JumpIfNot => Instruction::JumpIfNot(label),
            JumpIfNull => Instruction::JumpIfNull(label),
            JumpIfNotNull => Instruction::JumpIfNotNull(label),
            JumpIfEq => Instruction::JumpIfEq(label),
            JumpIfNotEq => Instruction::JumpIfNotEq(label),
            JumpIfEqConst(n) => Instruction::JumpIfEqConst(label, n),
            JumpIfNotEqConst(n) => Instruction::JumpIfNotEqConst(label, n),
        }
    }

    /// Length, in bytes, of this jump instruction.
    pub fn len(&self, short: bool) -> usize {
        use self::JumpInstruction::*;
        let len = if short { 1 } else { 2 };

        match *self {
            Jump |
            JumpIf |
            JumpIfNot |
            JumpIfNull |
            JumpIfNotNull |
            JumpIfEq |
            JumpIfNotEq => 1 + len,
            JumpIfBound(n) |
            JumpIfEqConst(n) |
            JumpIfNotEqConst(n) => {
                let op_len = if is_short_operand(n) { 1 } else { 2 };
                1 + len + op_len
            }
        }
    }
}

/// Represents a compiled bytecode function or expression.
#[derive(Clone, Debug)]
pub struct Code {
    /// Code object name, if present; top-level expressions and lambda code
    /// values do not have a name.
    pub name: Option<Name>,
    /// Const values referenced in bytecode
    pub consts: Box<[Value]>,
    /// Function body bytecode
    pub code: Box<[u8]>,
    /// Names of keyword parameters accepted in the order in which they are
    /// expected.
    pub kw_params: Box<[Name]>,
    /// Number of positional parameters accepted; this includes optional
    /// parameters, but excludes keyword and rest parameters, if accepted.
    /// Optional parameter values may be `Unbound`.
    pub n_params: u32,
    /// Number of positional parameters which must not be `Unbound`.
    pub req_params: u32,
    /// Miscellaneous flags; see `code_flags` for bit flag values.
    pub flags: u32,
    /// Optional documentation string
    pub doc: Option<String>,
}

impl Code {
    /// Returns the computed arity of the compiled function.
    pub fn arity(&self) -> Arity {
        if self.has_rest_params() {
            Arity::Min(self.req_params)
        } else {
            let kw = self.kw_params.len() as u32;
            let max = self.n_params + kw;
            if self.req_params == max {
                Arity::Exact(max)
            } else {
                Arity::Range(self.req_params, max)
            }
        }
    }

    /// Returns whether the function accepts a rest parameter.
    pub fn has_rest_params(&self) -> bool {
        self.flags & code_flags::PARAM_FLAGS_MASK == code_flags::HAS_REST_PARAMS
    }

    /// Returns whether the function accepts one or more keyword parameters.
    pub fn has_kw_params(&self) -> bool {
        self.flags & code_flags::PARAM_FLAGS_MASK == code_flags::HAS_KW_PARAMS
    }

    /// Returns whether all bytecode instructions can be executed without
    /// side effects.
    ///
    /// Such a code object typically results from compilation of compile-time
    /// operators.
    pub fn is_trivial(&self) -> bool {
        let mut r = CodeReader::new(&self.code, 0);
        let end = self.code.len();

        while r.offset() != end {
            match r.read_instruction() {
                Ok(instr) if instr.is_trivial() => (),
                _ => return false
            }
        }

        true
    }
}

/// Bit flag values for `Code::flags`
pub mod code_flags {
    /// Whether the code object has an associated name
    pub const HAS_NAME: u32         = 0x1;
    /// Whether the code accepts one or more keyword parameters
    pub const HAS_KW_PARAMS: u32    = 0x2;
    /// Whether the code accepts unbounded positional parameters
    pub const HAS_REST_PARAMS: u32  = 0x4;
    /// Mask of mutually exclusive parameter flags
    pub const PARAM_FLAGS_MASK: u32 = 0x6;
    /// Whether the code object has an associated docstring
    pub const HAS_DOC_STRING: u32   = 0x8;

    /// Mask of all valid flags
    pub const ALL_FLAGS: u32        = 0xf;
}

/// Reads `Instruction` values from a stream of bytes.
pub struct CodeReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CodeReader<'a> {
    /// Creates a new `CodeReader` wrapping a series of bytes.
    /// The first instruction will be read from `offset`.
    pub fn new(bytes: &[u8], offset: usize) -> CodeReader {
        CodeReader { bytes, offset }
    }

    /// Returns the offset, in bytes, at which the next instruction will be read.
    pub fn offset(&self) -> usize {
        self.offset
    }

    /// Reads an `Instruction` value from the byte stream.
    pub fn read_instruction(&mut self) -> Result<Instruction, ExecError> {
        Instruction::decode(self)
    }

    fn read_byte(&mut self) -> Result<u8, ExecError> {
        match self.bytes.get(self.offset).cloned() {
            Some(b) => {
                self.offset += 1;
                Ok(b)
            }
            None => Err(ExecError::UnexpectedEnd)
        }
    }

    fn read_operand(&mut self) -> Result<u32, ExecError> {
        let a = self.read_byte()? as u32;
        if a & 0x80 == 0 {
            Ok(a)
        } else {
            let a = (a & 0x7f) << 8;
            let b = self.read_byte()? as u32;
            Ok(a | b)
        }
    }
}

/// Contains a series of bytecode instructions
#[derive(Debug)]
pub struct CodeBlock {
    /// Encoded bytecode instructions
    bytes: Vec<u8>,
    /// Most recently added instruction; may be merged with next instruction
    instr_part: Option<Instruction>,
    /// Jump instruction added to the end of the block
    pub jump: Option<(JumpInstruction, u32)>,
    /// Refers to the block that immediately follows this block
    pub next: Option<u32>,
}

impl CodeBlock {
    /// Creates an empty `CodeBlock` with a small reserved buffer.
    pub fn new() -> CodeBlock {
        CodeBlock{
            bytes: Vec::with_capacity(16),
            instr_part: None,
            jump: None,
            next: None,
        }
    }

    /// Creates an empty `CodeBlock` without reserving data.
    pub fn empty() -> CodeBlock {
        CodeBlock{
            bytes: Vec::new(),
            instr_part: None,
            jump: None,
            next: None,
        }
    }

    /// Returns the final size of the block, including all encoded instructions
    /// and final jump instruction.
    /// `short` indicates whether jump instruction offsets are encoded in
    /// short format.
    ///
    /// If there is an unencoded instruction, its size is estimated.
    pub fn calculate_size(&self, short: bool) -> usize {
        let jump_len = self.jump.map_or(0, |(j, _)| j.len(short));
        let part_len = self.instr_part.map_or(0, |_| Instruction::max_len());

        self.bytes.len() + jump_len + part_len
    }

    /// Returns the size of all encoded instructions.
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns whether any intruction was encoded.
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns encoded bytecode data.
    ///
    /// `flush` should be called first to ensure all instructions are encoded.
    pub fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns whether the code block is mostly empty, permitting the compiler
    /// to prune it in some cases.
    pub fn is_mostly_empty(&self) -> bool {
        use self::Instruction::*;

        self.bytes.is_empty() && match self.instr_part {
            Some(Skip(_)) | Some(Return) | None => true,
            _ => false
        }
    }

    /// Sets the block which will immediately follow this block.
    ///
    /// May only be called once.
    pub fn set_next(&mut self, block: u32) {
        assert!(self.next.is_none());
        self.next = Some(block);
    }

    /// Sets the jump instruction at the end of the block.
    ///
    /// May only be called once.
    pub fn jump_to(&mut self, instr: JumpInstruction, block: u32) {
        assert!(self.jump.is_none());

        match self.instr_part.and_then(|i| merge_jump_instruction(i, instr)) {
            Some(j) => {
                self.instr_part = None;
                self.jump = Some((j, block));
            }
            None => self.jump = Some((instr, block))
        }
    }

    /// Write stored jump instruction to buffer, if present.
    pub fn write_jump(&mut self, label: u32, short: bool) -> Result<(), CompileError> {
        if let Some((instr, _)) = self.jump.take() {
            instr.set_label(label).encode(self, short)?;
        }
        Ok(())
    }

    /// Forcibly encodes a pending instruction.
    /// Does not encode a jump instruction.
    pub fn flush(&mut self) -> Result<(), CompileError> {
        if let Some(instr) = self.instr_part.take() {
            self.write_instruction(instr)
        } else {
            Ok(())
        }
    }

    /// Adds an instruction the block. The instruction may be stored until later
    /// to be merged into a combination instruction.
    pub fn push_instruction(&mut self, instr: Instruction) -> Result<(), CompileError> {
        if let Some(part) = self.instr_part {
            match merge_instructions(part, instr) {
                Some(new) => self.instr_part = Some(new),
                None => {
                    self.write_instruction(part)?;
                    self.instr_part = Some(instr);
                }
            }
        } else {
            self.instr_part = Some(instr);
        }
        Ok(())
    }

    fn write_instruction(&mut self, instr: Instruction) -> Result<(), CompileError> {
        instr.encode(self, false)
    }

    fn write_byte(&mut self, byte: u8) -> Result<(), CompileError> {
        self.bytes.push(byte);
        Ok(())
    }

    fn write_operand(&mut self, op: u32) -> Result<(), CompileError> {
        if is_short_operand(op) {
            self.write_short_operand(op)
        } else {
            self.write_long_operand(op)
        }
    }

    fn write_short_operand(&mut self, op: u32) -> Result<(), CompileError> {
        if is_short_operand(op) {
            self.write_byte(op as u8)
        } else {
            Err(CompileError::OperandOverflow(op))
        }
    }

    fn write_long_operand(&mut self, op: u32) -> Result<(), CompileError> {
        if op <= MAX_LONG_OPERAND {
            let lo = op as u8;
            let hi = (op >> 8) as u8;
            self.write_byte(hi | 0x80)?;
            self.write_byte(lo)
        } else {
            Err(CompileError::OperandOverflow(op))
        }
    }

    fn write_label_operand(&mut self, op: u32, short: bool) -> Result<(), CompileError> {
        if short {
            self.write_short_operand(op)
        } else {
            self.write_long_operand(op)
        }
    }
}

fn merge_jump_instruction(a: Instruction, b: JumpInstruction) -> Option<JumpInstruction> {
    use self::JumpInstruction::*;

    let j = match (a, b) {
        (Instruction::Not, JumpIf) => JumpIfNot,
        (Instruction::Not, JumpIfNot) => JumpIf,
        (Instruction::Null, JumpIf) => JumpIfNull,
        (Instruction::NotNull, JumpIf) => JumpIfNotNull,
        (Instruction::Null, JumpIfNot) => JumpIfNotNull,
        (Instruction::NotNull, JumpIfNot) => JumpIfNull,
        (Instruction::Eq, JumpIf) => JumpIfEq,
        (Instruction::NotEq, JumpIf) => JumpIfNotEq,
        (Instruction::Eq, JumpIfNot) => JumpIfNotEq,
        (Instruction::NotEq, JumpIfNot) => JumpIfEq,
        (Instruction::EqConst(n), JumpIf) => JumpIfEqConst(n),
        (Instruction::EqConst(n), JumpIfNot) => JumpIfNotEqConst(n),
        (Instruction::NotEqConst(n), JumpIf) => JumpIfNotEqConst(n),
        (Instruction::NotEqConst(n), JumpIfNot) => JumpIfEqConst(n),
        _ => return None
    };

    Some(j)
}

fn merge_instructions(a: Instruction, b: Instruction) -> Option<Instruction> {
    use self::Instruction::*;

    let new = match (a, b) {
        (Load(n), Push) => LoadPush(n),
        (LoadC(n), Push) => LoadCPush(n),
        (GetDef(n), Push) => GetDefPush(n),
        (Unit, Push) => UnitPush,
        (True, Push) => TruePush,
        (False, Push) => FalsePush,
        (First, Push) => FirstPush,
        (Tail, Push) => TailPush,
        (Init, Push) => InitPush,
        (Last, Push) => LastPush,
        (Const(n), Push) => ConstPush(n),
        (Null, Not) => NotNull,
        (NotNull, Not) => Null,
        (Eq, Not) => NotEq,
        (NotEq, Not) => Eq,
        (EqConst(n), Not) => NotEqConst(n),
        (NotEqConst(n), Not) => EqConst(n),
        (ApplySelf(n), Return) => TailApplySelf(n),
        (CallSelf(n), Return) => TailCallSelf(n),
        (Skip(_), Return) => Return,
        _ => return None
    };

    Some(new)
}

fn is_short_operand(op: u32) -> bool {
    op <= MAX_SHORT_OPERAND
}
