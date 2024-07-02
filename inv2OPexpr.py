
from lark import Lark, Transformer, v_args, exceptions
import re
import murphi

grammar = r"""

    ?const_decl:CNAME ":" INT
    ?consts:"const" (const_decl ";")*                     -> consts

    ?type_constr:CNAME                                    -> var_type        
        | (INT |CNAME) ".."  (INT |CNAME)                 -> range_type	
        | "boolean"                                       -> boolean_type
        | "scalarset" "(" CNAME ")"                       -> scalarset_type
        | "union" "{" type_constr ("," type_constr)* "}"  -> union_type
        | "enum" "{" CNAME ("," CNAME)* "}"               -> enum_type
        | "array" "[" type_constr "]" "of" type_constr    -> array_type
        | "record" (type_decl ";")* "end"                 -> record_type

    ?type_decl: CNAME ":" type_constr

    ?var_decl: CNAME ":" type_constr

    ?atom_expr: CNAME                                     -> unknown_expr
        | atom_expr "." CNAME                             -> field_name
        | atom_expr "[" expr "]"                          -> array_index
        | "forall" var_decl "do" expr "end"               -> forall_expr
        | "(" expr ")"

    ?neg_expr: "!" atom_expr                              -> neg_expr
        | atom_expr

    ?eq_expr: neg_expr "=" neg_expr                       -> eq_expr
        | neg_expr "!=" neg_expr                          -> ineq_expr
        | neg_expr

    ?and_expr: eq_expr "&" and_expr
        | eq_expr

    ?or_expr: and_expr "|" or_expr
        | and_expr

    ?imp_expr: or_expr "->" imp_expr
        | or_expr

    ?expr: imp_expr

    %import common.NEWLINE
    %import common.CNAME
    %import common.WS
    %import common.INT
    %import common.ESCAPED_STRING
    %import common.SIGNED_NUMBER    -> NUMBER
    %ignore WS

"""

@v_args(inline=True)
class MurphiTransformer(Transformer):
    def __init__(self):
        pass

    def const_decl(self, name, val):
        return murphi.MurphiConstDecl(str(name), val)

    def consts(self, *decls):
        return decls

    def int_const_rng(self,val):
        return(murphi.IntRngConst(int(val)))

    def name_const_rng(self,name):
        return(murphi.NameRngConst(name))

    def var_type(self, name):
        return murphi.VarType(str(name))

    def range_type(self, downRng,upRng):
        '''if downRng.isdigit():
            downRng=int(downRng)
        if upRng.isdigit():
            upRng=int(upRng)'''
        return murphi.RngType(str(downRng),str(upRng))

    def boolean_type(self):
        return murphi.BooleanType()

    def scalarset_type(self, const_name):
        return murphi.ScalarSetType(str(const_name))

    def union_type(self, *typs):
        return murphi.UnionType(typs)

    def enum_type(self, *names):
        return murphi.EnumType([str(name) for name in names])

    def array_type(self, idx_typ, ele_typ):
        return murphi.ArrayType(idx_typ, ele_typ)

    def record_type(self, *decls):
        return murphi.RecordType(decls)

    def type_decl(self, name, typ):
        return murphi.MurphiTypeDecl(str(name), typ)

    def var_decl(self, name, typ):
        return murphi.MurphiVarDecl(str(name), typ)

    def unknown_expr(self, name):
        return murphi.UnknownExpr(str(name))

    def field_name(self, v, field):
        return murphi.FieldName(v, field)

    def array_index(self, v, idx):
        return murphi.ArrayIndex(v, idx)

    def forall_expr(self, decl, expr):
        return murphi.ForallExpr(decl, expr)

    def neg_expr(self, expr):
        return murphi.NegExpr(expr)

    def eq_expr(self, expr1, expr2):
        return murphi.OpExpr("=", expr1, expr2)

    def ineq_expr(self, expr1, expr2):
        return murphi.OpExpr("!=", expr1, expr2)

    def and_expr(self, expr1, expr2):
        return murphi.OpExpr("&", expr1, expr2)

    def or_expr(self, expr1, expr2):
        return murphi.OpExpr("|", expr1, expr2)

    def imp_expr(self, expr1, expr2):
        return murphi.OpExpr("->", expr1, expr2)



murphi_parser = Lark(grammar, start="expr", parser="lalr", transformer=MurphiTransformer())

def parse_inv(filename, flag):
    protocol_name = filename
    rule = ''
    print("reading {} in {}...".format(flag, protocol_name))
    with open('./{}/{}.txt'.format(protocol_name, flag), 'r') as f:
        rule = f.read()
    inv_list = list(re.findall(r'rule_\w+:\s*(.*?)\n', rule, re.S))
    print("read success!, rules'len : {};\n example:\n{}".format(len(inv_list), inv_list[0]))
    inv_tree_list = []
    for inv in inv_list:
        inv_tree_list.append(murphi_parser.parse(inv))
    assert len(inv_tree_list) == len(inv_list)
    print('len of inv_tree : {};\nexample : \n{};\ntype of inv: {}'.format(len(inv_tree_list), inv_tree_list[0], type(inv_tree_list[0])))
    return inv_tree_list

def parse_single_inv(inv):
    return murphi_parser.parse(inv)

if __name__ == "__main__":
    flaglist = ['NI_InvAck1', 'NI_Local_GetX_PutX2', 'NI_Local_GetX_PutX3', 'NI_Remote_Get_Nak', 'NI_Remote_Get_Put', 'NI_Remote_Get_Put_Home', 'NI_Remote_GetX_Nak', 'NI_Remote_GetX_PutX_Home', 'NI_Remote_GetX_PutX', 'PI_Remote_PutX']
    for flag in flaglist:
        # parse_inv(filename = 'flash_ctc_10_origin', flag = flag)
        with open('./{}/temp_{}.txt'.format('flash_ctc_10_origin', flag), 'r') as f:
            rule = f.read()
            murphi_parser.parse(rule)