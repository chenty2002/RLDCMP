from typing import Dict, Iterable, List, Optional, Tuple
from utils import indent

class MurphiConstDecl:
    """Constant declaration in Murphi."""
    def __init__(self, name: str, val):
        assert isinstance(name, str)
        self.name = name
        self.val = val

    def __str__(self):
        return "%s : %s" % (self.name, self.val)

    def __repr__(self):
        return "MurphiConst(%s, %s)" % (self.name, self.val)

    def __eq__(self, other):
        return isinstance(other, MurphiConstDecl) and self.name == other.name and self.val == other.val


class MurphiType:
    """Base class for Murphi types."""
    pass

class VarType(MurphiType):
    """Murphi variable type."""
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "VarType(%s)" % self.name

    def __eq__(self, other):
        return isinstance(other, VarType) and self.name == other.name

class BooleanType(MurphiType):
    """Murphi boolean type."""
    def __init__(self):
        pass

    def __str__(self):
        return "boolean"

    def __repr__(self):
        return "BooleanType()"

    def __eq__(self, other):
        return isinstance(other, BooleanType)

class ScalarSetType(MurphiType):
    """Murphi scalar set type."""
    def __init__(self, const_name: str):
        assert isinstance(const_name, str)
        self.const_name = const_name

    def __str__(self):
        return "scalarset(%s)" % self.const_name

    def __repr__(self):
        return "ScalarSetType(%s)" % self.const_name

    def __eq__(self, other):
        return isinstance(other, ScalarSetType) and self.const_name == other.const_name

class UnionType(MurphiType):
    """Murphi union type."""
    def __init__(self, typs):
        self.typs = typs

    def __str__(self):
        return "union {%s}" % (', '.join(str(typ) for typ in self.typs))

    def __repr__(self):
        return "UnionType(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, UnionType) and self.typs == other.typs

class EnumType(MurphiType):
    """Murphi enum type."""
    def __init__(self, names):
        self.names = names

    def __str__(self):
        return "enum {%s}" % (', '.join(name for name in self.names))

    def __repr__(self):
        return "EnumType(%s)" % (', '.join(repr(name) for name in self.names))

    def __eq__(self, other):
        return isinstance(other, EnumType) and self.names == other.names

class ArrayType(MurphiType):
    """Murphi array type."""
    def __init__(self, idx_typ, ele_typ):
        self.idx_typ = idx_typ
        self.ele_typ = ele_typ

    def __str__(self):
        return "array [%s] of %s" % (self.idx_typ, self.ele_typ)

    def __repr__(self):
        return "ArrayType(%s, %s)" % (repr(self.idx_typ), repr(self.ele_typ))

    def __eq__(self, other):
        return isinstance(other, ArrayType) and self.idx_typ == other.idx_typ and \
            self.ele_typ == other.ele_typ

class RecordType(MurphiType):
    """Murphi record type."""
    def __init__(self, typ_decls):
        self.typ_decls = typ_decls

    def __str__(self):
        return "record\n%s\nend" % ('\n'.join(indent(str(decl), 2) + ';' for decl in self.typ_decls))

    def __repr__(self):
        return "RecordType(%s)" % (', '.join(repr(decl) for decl in self.typ_decls))

    def __eq__(self, other):
        return isinstance(other, RecordType) and self.typ_decls == other.typ_decls

class MurphiTypeDecl:
    """Murphi type declaration."""
    def __init__(self, name: str, typ: MurphiType):
        assert isinstance(name, str) and isinstance(typ, MurphiType)
        self.name = name
        self.typ = typ

    def __str__(self):
        return "%s : %s" % (self.name, self.typ)

    def __repr__(self):
        return "MurphiTypeDecl(%s, %s)" % (repr(self.name), repr(self.typ))

    def __eq__(self, other):
        return isinstance(other, MurphiTypeDecl) and self.name == other.name and \
            self.typ == other.typ

class MurphiVarDecl:
    """Murphi variable declaration."""
    def __init__(self, name, typ):
        assert isinstance(name, str) and isinstance(typ, MurphiType)
        self.name = name
        self.typ = typ

    def __str__(self):
        return "%s : %s" % (self.name, self.typ)

    def __repr__(self):
        return "MurphiVarDecl(%s, %s)" % (repr(self.name), repr(self.typ))

    def __eq__(self, other):
        return isinstance(other, MurphiVarDecl) and self.name == other.name and \
            self.typ == other.typ

class MurphiExpr:
    """Base class for Murphi expressions."""
    def priority(self) -> int:
        raise NotImplementedError

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiExpr":
        return self


class UnknownExpr(MurphiExpr):
    """Unknown expression in Murphi."""
    def __init__(self, s):
        assert isinstance(s, str)
        self.s = s

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "%s" % self.s

    def __repr__(self):
        return "UnknownExpr(%s)" % repr(self.s)

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> MurphiExpr:
        assert isinstance(prot, MurphiProtocol)
        if self.s == "true":
            return BooleanExpr(True)
        elif self.s == "false":
            return BooleanExpr(False)
        elif self.s in prot.enum_map:
            return EnumValExpr(prot.enum_map[self.s], self.s)
        elif self.s in bound_vars:
            return VarExpr(self.s, bound_vars[self.s])
        elif self.s in prot.var_map:
            return VarExpr(self.s, prot.var_map[self.s])
        else:
            raise AssertionError("elaborate: unrecognized name %s" % self.s)

class BooleanExpr(MurphiExpr):
    """Boolean expression in Murphi."""
    def __init__(self, val):
        self.val = val

    def priority(self) -> int:
        return 100

    def __str__(self):
        if self.val:
            return "true"
        else:
            return "false"

    def __repr__(self):
        return "BooleanExpr(%s)" % repr(self.val)

    def __eq__(self, other):
        return isinstance(other, BooleanExpr) and self.val == other.val

class EnumValExpr(MurphiExpr):
    """Enum values in Murphi."""
    def __init__(self, enum_type, enum_val):
        self.enum_type = enum_type
        self.enum_val = enum_val

    def priority(self) -> int:
        return 100

    def __str__(self):
        return self.enum_val

    def __repr__(self):
        return "EnumValExpr(%s, %s)" % (repr(self.enum_type), repr(self.enum_val))

    def __eq__(self, other):
        return isinstance(other, EnumValExpr) and self.enum_type == other.enum_type and \
            self.enum_val == other.enum_val

class VarExpr(MurphiExpr):
    """Variable in Murphi."""
    def __init__(self, name: str, typ: MurphiType):
        assert isinstance(name, str) and isinstance(typ, MurphiType)
        self.name = name
        self.typ = typ

    def priority(self) -> int:
        return 100

    def __str__(self):
        return str(self.name)

    def __repr__(self):
        return "VarExpr(%s)" % repr(self.name)

    def __eq__(self, other):
        return isinstance(other, VarExpr) and self.name == other.name and self.typ == other.typ

class FieldName(MurphiExpr):
    """Field access in Murphi."""
    def __init__(self, v: MurphiExpr, field: str):
        assert isinstance(v, MurphiExpr)
        assert isinstance(field, str)
        self.v = v
        self.field = field

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "%s.%s" % (self.v, self.field)

    def __repr__(self):
        return "FieldName(%s, %s)" % (repr(self.v), repr(self.field))

    def __eq__(self, other):
        return isinstance(other, FieldName) and self.v == other.v and self.field == other.field

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> MurphiExpr:
        return FieldName(self.v.elaborate(prot, bound_vars), self.field)

class ArrayIndex(MurphiExpr):
    """Array indexing expression in Murphi."""
    def __init__(self, v: MurphiExpr, idx: MurphiExpr):
        self.v = v
        self.idx = idx

    def priority(self) -> int:
        return 100

    def __str__(self):
        return "%s[%s]" % (self.v, self.idx)

    def __repr__(self):
        return "ArrayIndex(%s, %s)" % (repr(self.v), repr(self.idx))

    def __eq__(self, other):
        return isinstance(other, ArrayIndex) and self.v == other.v and self.idx == other.idx

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> MurphiExpr:
        return ArrayIndex(self.v.elaborate(prot, bound_vars), self.idx.elaborate(prot, bound_vars))

class ForallExpr(MurphiExpr):
    """Forall expression in Murphi."""
    def __init__(self, var_decl: MurphiVarDecl, expr: MurphiExpr):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.expr = expr

    def priority(self) -> int:
        return 70

    def __str__(self):
        res = "forall %s do\n" % self.var_decl
        res += indent(str(self.expr), 2) + "\n"
        res += "end"
        return res

    def __repr__(self):
        return "ForallExpr(%s, %s)" % (repr(self.var_decl), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, ForallExpr) and self.var_decl == other.var_decl and \
            self.expr == other.expr

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> MurphiExpr:
        bound_vars[self.var] = self.typ
        res = ForallExpr(self.var_decl, self.expr.elaborate(prot, bound_vars))
        del bound_vars[self.var]
        return res

priority_map = {
    '+': 60,
    '=': 50,
    '!=': 50,
    '&': 35,
    '|': 30,
    '->': 25
}

class OpExpr(MurphiExpr):
    """Operator in Murphi.
    
    Currently we support comparison and boolean operators.
    
    """
    def __init__(self, op: str, expr1: MurphiExpr, expr2: MurphiExpr):
        assert isinstance(op, str) and op in ("+", '=', '!=', '&', '|', '->')
        assert isinstance(expr1, MurphiExpr), "OpExpr: expr1 %s has type %s" % (expr1, type(expr1))
        assert isinstance(expr2, MurphiExpr), "OpExpr: expr2 %s has type %s" % (expr2, type(expr2))
        self.op = op
        self.expr1 = expr1
        self.expr2 = expr2

    def priority(self) -> int:
        return priority_map[self.op]

    def __str__(self):
        s1, s2 = str(self.expr1), str(self.expr2)
        if self.expr1.priority() <= self.priority():
            if '\n' in s1:
                s1 = "(" + indent(s1, 2, first_line=1) + " )"
            else:
                s1 = "(" + s1 + ")"
        if self.expr2.priority() < self.priority():
            if '\n' in s2:
                s2 = "(" + indent(s2, 2, first_line=1) + " )"
            else:
                s2 = "(" + s2 + ")"
        if self.op in ("=", "!="):
            return "%s %s %s" % (s1, self.op, s2)
        elif self.op in ('&', '|'):
            return "%s %s\n%s" % (s1, self.op, s2)
        elif self.op in ('->'):
            if isinstance(self.expr2, OpExpr) and self.expr2.op == '->':
                return "%s ->\n(%s)" % (s1, indent(s2, 2))
            else:
                return "%s ->\n%s" % (s1, indent(s2, 2))
        else:
            raise NotImplementedError

    def __repr__(self):
        return "OpExpr(%s, %s, %s)" % (self.op, self.expr1, self.expr2)

    def __eq__(self, other):
        return isinstance(other, OpExpr) and self.op == other.op and self.expr1 == other.expr1 and \
            self.expr2 == other.expr2

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> MurphiExpr:
        return OpExpr(self.op, self.expr1.elaborate(prot, bound_vars), self.expr2.elaborate(prot, bound_vars))

class NegExpr(MurphiExpr):
    """Negation expression in Murphi."""
    def __init__(self, expr: MurphiExpr):
        self.expr = expr

    def priority(self) -> int:
        return 80

    def __str__(self):
        s = str(self.expr)
        if self.expr.priority() < self.priority():
            s = "(" + s + ")"
        return "!" + s
    
    def __repr__(self):
        return "NegExpr(%s)" % self.expr

    def __eq__(self, other):
        return isinstance(other, NegExpr) and self.expr == other.expr

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> MurphiExpr:
        return NegExpr(self.expr.elaborate(prot, bound_vars))

class MurphiCmd:
    """Base class for Murphi commands."""
    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiCmd":
        return self

class Skip(MurphiCmd):
    """Skip command in Murphi."""
    def __init__(self):
        pass

    def __str__(self):
        return "skip;"

    def __repr__(self):
        return "Skip()"

    def __eq__(self, other):
        return isinstance(other, Skip)

class UndefineCmd(MurphiCmd):
    """Undefine command in Murphi."""
    def __init__(self, var: MurphiExpr):
        assert isinstance(var, MurphiExpr)
        self.var = var

    def __str__(self):
        return "undefine %s;" % self.var

    def __repr__(self):
        return "UndefineCmd(%s)" % repr(self.var)

    def __eq__(self, other):
        return isinstance(other, UndefineCmd) and self.var == other.var

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiCmd":
        return UndefineCmd(self.var.elaborate(prot, bound_vars))

class AssignCmd(MurphiCmd):
    """Assignment command in Murphi."""
    def __init__(self, var: MurphiExpr, expr: MurphiExpr):
        assert isinstance(var, MurphiExpr)
        assert isinstance(expr, MurphiExpr)
        self.var = var
        self.expr = expr

    def __str__(self):
        return "%s := %s;" % (self.var, self.expr) 

    def __repr__(self):
        return "AssignCmd(%s, %s)" % (repr(self.var), repr(self.expr))

    def __eq__(self, other):
        return isinstance(other, AssignCmd) and self.var == other.var and self.expr == other.expr

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiCmd":
        return AssignCmd(self.var.elaborate(prot, bound_vars), self.expr.elaborate(prot, bound_vars))

class ForallCmd(MurphiCmd):
    """Forall command in Murphi."""
    def __init__(self, var_decl: MurphiVarDecl, cmds: Iterable[MurphiCmd]):
        self.var_decl = var_decl
        self.var, self.typ = self.var_decl.name, self.var_decl.typ
        self.cmds = tuple(cmds)

    def __str__(self):
        res = "for %s do\n" % self.var_decl
        for cmd in self.cmds:
            res += indent(str(cmd), 2) + "\n"
        res += "end;"
        return res

    def __repr__(self):
        return "ForallCmd(%s, %s)" % (repr(self.var_decl), repr(self.cmds))

    def __eq__(self, other):
        return isinstance(other, ForallCmd) and self.var_decl == other.var_decl and \
            self.cmds == other.cmds

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiCmd":
        bound_vars[self.var] = self.typ
        res = ForallCmd(self.var_decl, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])
        del bound_vars[self.var]
        return res

class IfCmd(MurphiCmd):
    """If-then-else command in Murphi."""
    def __init__(self, args: Iterable[MurphiExpr | Iterable[MurphiCmd]]):
        assert len(args) >= 2, "IfCmd: input args has %s elements" % len(args)
        self.args = args

        self.if_branches: List[Tuple[MurphiExpr, MurphiCmd]] = []
        self.else_branch: Optional[MurphiCmd] = None
        for i in range(len(self.args) // 2):
            self.if_branches.append((self.args[2*i], self.args[2*i+1]))
        if len(self.args) % 2 == 1:
            self.else_branch = self.args[-1]

    def __str__(self):
        res = "if %s then\n" % self.if_branches[0][0]
        for cmd in self.if_branches[0][1]:
            res += indent(str(cmd), 2) + "\n"
        for i in range(1, len(self.if_branches)):
            res += "elsif %s then\n" % self.if_branches[i][0]
            for cmd in self.if_branches[i][1]:
                res += indent(str(cmd), 2) + "\n"
        if self.else_branch:
            res += "else\n"
            for cmd in self.else_branch:
                res += indent(str(cmd), 2) + "\n"
        res += "end;"
        return res

    def __repr__(self):
        return "IfCmd(%s)" % repr(self.args)

    def __eq__(self, other):
        return isinstance(other, IfCmd) and self.args == other.args

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiCmd":
        new_args = []
        for arg in self.args:
            if isinstance(arg, MurphiExpr):
                new_args.append(arg.elaborate(prot, bound_vars))
            else:
                new_args.append([cmd.elaborate(prot, bound_vars) for cmd in arg])
        return IfCmd(new_args)

class StartState:
    """Specification of starting state in Murphi."""
    def __init__(self, name: str, cmds: Iterable[MurphiCmd]):
        self.name = name
        self.cmds = tuple(cmds)

    def __str__(self):
        res = "startstate \"%s\"\n" % self.name
        for cmd in self.cmds:
            res += indent(str(cmd), 2) + "\n"
        res += "endstartstate;"
        return res
    
    def __repr__(self):
        return "StartState(%s, %s)" % (repr(self.name), repr(self.cmds))

    def elaborate(self, prot, bound_vars):
        return StartState(self.name, [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])

class MurphiDecl:
    """Base class for Murphi declarations."""
    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiDecl":
        raise NotImplementedError


class MurphiRule:
    """Representation of rules in Murphi."""
    def __init__(self, name: str, cond: MurphiExpr, cmds: Iterable[MurphiCmd]):
        assert isinstance(name, str)
        assert isinstance(cond, MurphiExpr)
        assert all(isinstance(cmd, MurphiCmd) for cmd in cmds)
        self.name = name
        self.cond = cond
        self.cmds = tuple(cmds)

    def __str__(self):
        res = "rule \"%s\"\n" % self.name
        res += indent(str(self.cond), 2) + "\n"
        res += "==>\n"
        res += "begin\n"
        for cmd in self.cmds:
            res += indent(str(cmd), 2) + "\n"
        res += "endrule;"
        return res

    def __repr__(self):
        return "MurphiRule(%s, %s, %s)" % (repr(self.name), repr(self.cond), repr(self.cmds))

    def __eq__(self, other):
        return isinstance(other, MurphiRule) and self.name == other.name and \
            self.cond == other.cond and self.cmds == other.cmds

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiDecl":
        return MurphiRule(self.name, self.cond.elaborate(prot, bound_vars),
                          [cmd.elaborate(prot, bound_vars) for cmd in self.cmds])

    def addSpecialGuard(self,f):
        self.cond = OpExpr("&",f,self.cond)


class MurphiRuleSet:
    """Rulesets in Murphi."""
    def __init__(self, var_decls: Iterable[MurphiVarDecl], rule: MurphiRule | StartState):
        assert all(isinstance(var_decl, MurphiVarDecl) for var_decl in var_decls)
        assert isinstance(rule, MurphiRule) or isinstance(rule, StartState)
        self.var_decls = var_decls
        self.var_map = dict()
        for var_decl in self.var_decls:
            self.var_map[var_decl.name] = var_decl.typ
        self.rule = rule

    def __str__(self):
        res = "ruleset %s do\n" % ("; ".join(str(var_decl) for var_decl in self.var_decls))
        res += str(self.rule) + "\n"
        res += "endruleset;"
        return res

    def __repr__(self):
        return "MurphiRuleSet(%s, %s)" % (repr(self.var_decls), repr(self.rule))

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiDecl":
        for var, typ in self.var_map.items():
            bound_vars[var] = typ
        res = MurphiRuleSet(self.var_decls, self.rule.elaborate(prot, bound_vars))
        for var in self.var_map:
            del bound_vars[var]
        return res

class MurphiInvariant:
    """Invariants in Murphi."""
    def __init__(self, name: str, inv: MurphiExpr):
        assert isinstance(name, str)
        assert isinstance(inv, MurphiExpr)
        self.name = name
        self.inv = inv

    def __str__(self):
        res = "invariant \"%s\"\n" % self.name
        res += indent(str(self.inv), 2)
        res +=";\n"
        return res

    def __repr__(self):
        return "Invariant(%s, %s)" % (repr(self.name), repr(self.inv))

    def __eq__(self, other):
        return isinstance(other, MurphiInvariant) and self.name == other.name and \
            self.inv == other.inv

    def elaborate(self, prot: "MurphiProtocol", bound_vars: Dict[str, MurphiType]) -> "MurphiDecl":
        return MurphiInvariant(self.name, self.inv.elaborate(prot, bound_vars))


class MurphiProtocol:
    """Internal representation of a Murphi protocol."""
    def __init__(self, consts: Iterable[MurphiConstDecl],
                 types: Iterable[MurphiTypeDecl],
                 vars: Iterable[MurphiVarDecl],
                 start_state: StartState | MurphiRuleSet,
                 decls: Iterable[MurphiDecl]):
        self.consts = tuple(consts)
        self.types = tuple(types)
        self.vars = tuple(vars)
        self.start_state = start_state
        self.decls = tuple(decls)

        # Process types
        self.typ_map = dict()
        self.enum_typ_map = dict()
        self.enum_map = dict()
        for typ_decl in self.types:
            self.typ_map[typ_decl.name] = typ_decl.typ
            if isinstance(typ_decl.typ, EnumType):
                self.enum_typ_map[typ_decl.name] = typ_decl.typ
                for enum_val in typ_decl.typ.names:
                    self.enum_map[enum_val] = typ_decl.typ

        # Process variables
        self.var_map = dict()
        for var_decl in self.vars:
            self.var_map[var_decl.name] = var_decl.typ

        # Elaboration
        if isinstance(start_state, MurphiRuleSet):
            self.start_state = MurphiRuleSet(start_state.var_decls, self.start_state.rule.elaborate(self, start_state.var_map))
        else:
            self.start_state = self.start_state.elaborate(self, dict())        
        self.decls = [decl.elaborate(self, dict()) for decl in self.decls]

        # Divide into categories
        self.rule_map = dict()
        self.ori_rule_map = dict()
        self.abs_rule_map = dict()
        self.inv_map = dict()
        self.ori_inv_map = dict()
        self.lemma_map = dict()

        for decl in self.decls:
            if isinstance(decl, MurphiRule):
                self.rule_map[decl.name] = decl
                if decl.name.startswith("ABS_"):
                    self.abs_rule_map[decl.name] = decl
                else:
                    self.ori_rule_map[decl.name] = decl
            elif isinstance(decl, MurphiRuleSet):
                self.rule_map[decl.rule.name] = decl
                if decl.rule.name.startswith("ABS_"):
                    self.abs_rule_map[decl.rule.name] = decl
                else:
                    self.ori_rule_map[decl.rule.name] = decl
            elif isinstance(decl, MurphiInvariant):
                self.inv_map[decl.name] = decl
                if decl.name.startswith("Lemma_"):
                    self.lemma_map[decl.name] = decl
                else:
                    self.ori_inv_map[decl.name] = decl
            else:
                raise NotImplementedError

    def add_lemma(self, decl: MurphiInvariant):
        assert isinstance(decl, MurphiInvariant)
        self.decls.append(decl)
        self.inv_map[decl.name] = decl
        self.lemma_map[decl.name] = decl

    def add_abs_rule(self, decl: MurphiRule | MurphiRuleSet):
        assert isinstance(decl, (MurphiRule, MurphiRuleSet))
        self.decls.append(decl)

        if isinstance(decl, MurphiRule):
            self.rule_map[decl.name] = decl
            self.abs_rule_map[decl.name] = decl
        elif isinstance(decl, MurphiRuleSet):
            self.rule_map[decl.rule.name] = decl
            self.abs_rule_map[decl.rule.name] = decl

    def addition(self):
        for k in self.ori_rule_map.keys():
            r = self.ori_rule_map[k]
            if isinstance(r, MurphiRuleSet):
                if len(r.var_decls) == 2:
                    for ak in self.abs_rule_map.keys():
                        if ak==("ABS_"+ k+ "_"+ r.var_decls[0].name ):
                            ar=self.abs_rule_map[ak]
                            addf=NegExpr(OpExpr("=",EnumValExpr(None,"Other"),VarExpr(name=r.var_decls[1].name,typ=r.var_decls[1].typ)))
                            ar.rule.addSpecialGuard(addf)
                        elif  ak==("ABS_"+k+"_"+r.var_decls[1].name):
                            ar=self.abs_rule_map[ak]
                            addf=NegExpr(OpExpr("=",VarExpr(name=r.var_decls[0].name,typ=r.var_decls[0].typ),EnumValExpr(None,"Other")))
                            ar.rule.addSpecialGuard(addf)
                        else:
                            pass

    def __str__(self):
        res = "const\n\n"
        for const in self.consts:
            res += indent(str(const), 2) + ";\n\n"
        res += "type\n\n"
        for typ in self.types:
            res += indent(str(typ), 2) + ";\n\n"
        res += "var\n\n"
        for var in self.vars:
            res += indent(str(var), 2) + ";\n\n"
        res += str(self.start_state) + "\n\n"
        for decl in self.decls:
            res += str(decl) + "\n\n"
        return res

    def __repr__(self):
        return "MurphiProtocol(%s, %s, %s)" % (repr(self.consts), repr(self.types), repr(self.vars))