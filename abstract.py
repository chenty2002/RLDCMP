import murphi
import murphiparser as parser
from muserv.muserv import MurphiChk
import re
import os
import time 
import copy

#from settings import MAX_SLEEP_TIME, TIME_OUT, SMV_PATH, SMV_FILE_DIR, HOST, PORT
import inv2OPexpr
from settings import MU_PATH, MU_INCLUDE, GXX_PATH, MU_FILE_DIR, MU_CHECK_TIMEOUT, MU_CHECK_MEMORY
from learn_and_abs import DataProcess, RuleLearing
from analyser import Protocol, analyzeParams, inv_strengthen, number_type
from process import to_murphi, seperation
from murphi_process import murphi_screen

class DontCareExpr(murphi.MurphiExpr):
    def __init__(self):
        pass

    def priority(self):
        return 100

    def __str__(self):
        return "DontCare"

    def __repr__(self):
        return "DontCareExpr()"

def safeVar(e, limits):
    if isinstance(e, murphi.VarExpr):
        return True
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        if not isinstance(e.idx, murphi.VarExpr) or e.idx.name not in limits:
            raise NotImplementedError("safeVar on %s" % e)
        return limits[e.idx.name]
    else:
        raise NotImplementedError("safeVar on %s" % e)

def safeExp(e, limits):
    if isinstance(e, murphi.BooleanExpr):
        return True
    elif isinstance(e, murphi.EnumValExpr):
        return True
    elif isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType):
            if e.typ.name == "NODE":
                if e.name not in limits:
                    raise NotImplementedError("safeExp on %s" % e)
                return limits[e.name]
            else:
                return True
        elif isinstance(e.typ, murphi.BooleanType):
            return safeVar(e, limits)
        elif isinstance(e.typ, murphi.EnumType):
            return safeVar(e, limits)
        else:
            raise NotImplementedError("safeExp on %s" % e)
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return safeVar(e, limits)
    else:
        raise NotImplementedError("safeExp on %s" % e)

def safeForm(e, limits):
    if isinstance(e, murphi.OpExpr):
        if e.op in ('=', '!='):
            return safeExp(e.expr1, limits) and safeExp(e.expr2, limits)
        elif e.op in ('&', '|', '->'):
            return safeForm(e.expr1, limits) and safeForm(e.expr2, limits)
        else:
            raise NotImplementedError("safeForm on %s" % e)
    elif isinstance(e, murphi.NegExpr):
        return safeForm(e.expr, limits)
    elif isinstance(e, murphi.ForallExpr):
        return False
    elif isinstance(e, (murphi.BooleanExpr, murphi.VarExpr, murphi.FieldName, murphi.ArrayIndex)):
        return safeExp(e, limits)
    else:
        raise NotImplementedError("safeForm on %s" % e)

def boundVar(e, i):
    # print('e is {}'.format(e))
    # print('boundform is {}'.format(boundVar(e,i)))
    if isinstance(e, murphi.VarExpr):
        return True
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return isinstance(e.idx, murphi.VarExpr) and e.idx.name == i
    else:
        raise NotImplementedError("boundVar on %s" % e)

def boundExp(e, i):
    if isinstance(e, murphi.BooleanExpr):
        return True
    elif isinstance(e, murphi.EnumValExpr):
        return True
    elif isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType) and e.typ.name == "NODE":
            return e.name == i
        elif isinstance(e.typ, murphi.BooleanType):
            return boundVar(e, i)
        elif isinstance(e.typ, murphi.EnumType):
            return boundVar(e, i)
        else:
            # raise NotImplementedError("boundExp on %s" % e)
            return True
    elif isinstance(e, murphi.FieldName):
        return True
    elif isinstance(e, murphi.ArrayIndex):
        return boundVar(e, i)
    else:
        raise NotImplementedError("boundExp on %s" % e)

def boundForm(e, i):
    if isinstance(e, murphi.OpExpr):
        if e.op in ('=', '!='):
            return boundVar(e.expr1, i) and boundExp(e.expr2, i)
        elif e.op in ('&', '|', '->'):
            return boundForm(e.expr1, i) and boundForm(e.expr2, i)
        else:
            raise NotImplementedError("boundForm on %s" % e)
    elif isinstance(e, murphi.NegExpr):
        return boundForm(e.expr, i)
    elif isinstance(e, murphi.ForallExpr):
        return False
    elif isinstance(e, (murphi.BooleanExpr, murphi.VarExpr, murphi.FieldName, murphi.ArrayIndex)):
        return boundExp(e, i)
    else:
        raise NotImplementedError("boundForm on %s" % e)

def boundStatement(cmd, i):
    if isinstance(cmd, murphi.Skip):
        return True
    elif isinstance(cmd, murphi.AssignCmd):
        if isinstance(cmd.expr, murphi.OpExpr):
            return boundVar(cmd.var, i) and boundForm(cmd.expr, i)
        else:
            return boundVar(cmd.var, i) and boundExp(cmd.expr, i)
    elif isinstance(cmd, murphi.IfCmd):
        for cond, cmds in cmd.if_branches:
            if not boundForm(cond, i):
                return False
            if not all(boundStatement(c, i) for c in cmds):
                return False
        if cmd.else_branch:
            if not all(boundStatement(c, i) for c in cmd.else_branch):
                return False
        return True
    elif isinstance(cmd, murphi.ForallCmd):
        return False
    else:
        return NotImplementedError("boundStatement on %s" % cmd)

def absTransfConst(e, limits):
    if isinstance(e, murphi.BooleanExpr):
        return e
    elif isinstance(e, murphi.EnumValExpr):
        return e
    elif isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType) and e.typ.name == "NODE":
            if limits[e.name]:
                return e
            else:
                return murphi.EnumValExpr(murphi.EnumType(["Other"]), "Other")
        else:
            raise NotImplementedError("absTransfConst on %s" % e)
    else:
        raise NotImplementedError("absTransfConst on %s" % e)

def absTransfVar(e, limits):
    if isinstance(e, murphi.VarExpr):
        if isinstance(e.typ, murphi.VarType) and e.typ.name == "NODE":
            return absTransfConst(e, limits)
        else:
            return e
    elif isinstance(e, murphi.FieldName):
        abs_v = absTransfVar(e.v, limits)
        if isinstance(abs_v, DontCareExpr):
            return DontCareExpr()
        else:
            return murphi.FieldName(abs_v, e.field)
    elif isinstance(e, murphi.ArrayIndex):
        if not isinstance(e.idx, murphi.VarExpr) or e.idx.name not in limits:
            raise NotImplementedError("absTransfVar on %s" % e)
        if limits[e.idx.name]:
            return e
        else:
            return DontCareExpr()
    elif isinstance(e, DontCareExpr):
        return DontCareExpr()
    else:
        raise NotImplementedError("absTransfVar on %s" % e)

def absTransfExp(e, limits):
    if isinstance(e, murphi.BooleanExpr):
        return absTransfConst(e, limits)
    elif isinstance(e, murphi.EnumValExpr):
        return absTransfConst(e, limits)
    elif isinstance(e, murphi.VarExpr):
        return absTransfVar(e, limits)
    elif isinstance(e, murphi.FieldName):
        return absTransfVar(e, limits)
    elif isinstance(e, murphi.ArrayIndex):
        return absTransfVar(e, limits)
    elif isinstance(e, DontCareExpr()):
        return DontCareExpr()
    else:
        raise NotImplementedError("absTransfExp on %s" % e)

def check_forall_exclude_form(e):
    """If e is of the form forall j : NODE do j != i -> P, return (i, P).
    Otherwise, return None.
    
    """
    if isinstance(e, murphi.ForallExpr):
        if is_imp(e.expr):
            assm, concl = e.expr.expr1, e.expr.expr2
            if assm.op == '!=' and assm.expr1.name == e.var and isinstance(assm.expr2, murphi.VarExpr):
                return assm.expr2.name, concl

def check_forall_exclude_cmd(c):
    """If c is of the form for j : NODE do if (j != i) then S end, return (i, S).
    Otherwise, return None.
    
    """
    if isinstance(c, murphi.ForallCmd):
        # print(c.cmds, len(c.cmds), c.cmds[0].args)
        if len(c.cmds) == 1 and isinstance(c.cmds[0], murphi.IfCmd) and len(c.cmds[0].args) == 2:
            cond, cmds = c.cmds[0].args
            if cond.op == '!=' and cond.expr1.name == c.var and isinstance(cond.expr2, murphi.VarExpr):
                return cond.expr2.name, cmds

class Abstraction():
    def __init__(self, rule, limits):
        self.rule = rule
        self.limits = limits
        self.replacement = dict()

    def absTransfForm(self, e, limits):
        if isinstance(e, murphi.OpExpr):
            if e.op == '=':
                abs_e1, abs_e2 = absTransfExp(e.expr1, limits), absTransfExp(e.expr2, limits)
                if isinstance(abs_e1, DontCareExpr):
                    if isinstance(abs_e2, murphi.FieldName):
                        value = abs_e2.v
                        if not isinstance(value, murphi.ArrayIndex):
                            self.replacement[str(e.expr1)] = e.expr2
                    elif isinstance(abs_e2, murphi.VarExpr):
                        self.replacement[str(e.expr1)] = e.expr2
                    return DontCareExpr()
                else:
                    return murphi.OpExpr(e.op, abs_e1, abs_e2)
            elif e.op == '!=':
                abs_e1, abs_e2 = absTransfExp(e.expr1, limits), absTransfExp(e.expr2, limits)
                if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr) or \
                    not safeForm(murphi.OpExpr('=', e.expr1, e.expr2), limits):
                    return DontCareExpr()
                else:
                    return murphi.OpExpr(e.op, abs_e1, abs_e2)
            elif e.op == '&':
                abs_e1, abs_e2 = self.absTransfForm(e.expr1, limits), self.absTransfForm(e.expr2, limits)
                # print('before: \nexpr1 is {}; \nexpr2 is {}'.format(e.expr1, e.expr2))
                # print('after: \nexpr1 is {}; \nexpr2 is {}'.format(abs_e1, abs_e2))
                if isinstance(abs_e1, DontCareExpr):
                    return abs_e2
                elif isinstance(abs_e2, DontCareExpr):
                    return abs_e1
                else:
                    return murphi.OpExpr(e.op, abs_e1, abs_e2)
            elif e.op == '|':
                abs_e1, abs_e2 = self.absTransfForm(e.expr1, limits), self.absTransfForm(e.expr2, limits)
                if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr):
                    return DontCareExpr()
                else:
                    return murphi.OpExpr(e.op, abs_e1, abs_e2)
            elif e.op == '->':
                abs_e1, abs_e2 = self.absTransfForm(e.expr1, limits), self.absTransfForm(e.expr2, limits)
                if isinstance(abs_e1, DontCareExpr) or isinstance(abs_e2, DontCareExpr) or \
                    not safeForm(e.expr1, limits):
                    # print(isinstance(abs_e1, DontCareExpr), isinstance(abs_e2, DontCareExpr), safeForm(e.expr1, limits))
                    return DontCareExpr()
                else:
                    return murphi.OpExpr(e.op, abs_e1, abs_e2)
            else:
                raise NotImplementedError("absTransfForm on %s" % e)
        elif isinstance(e, murphi.NegExpr):
            abs_e = self.absTransfForm(e.expr, limits)
            if isinstance(abs_e, DontCareExpr) or not safeForm(e, limits):
                return DontCareExpr()
            else:
                return murphi.NegExpr(abs_e)
        elif isinstance(e, murphi.ForallExpr):
            # First, check for ForallExcl case
            excl_form = check_forall_exclude_form(e)
            if excl_form:
                excl_var, concl = excl_form
                if excl_var in limits and boundForm(concl, e.var):
                    if limits[excl_var]:
                        return e
                    else:
                        return murphi.ForallExpr(e.var_decl, concl)
                else:
                    return DontCareExpr()
            elif boundForm(e.expr, e.var):
                return e
            else:
                return DontCareExpr()
        elif isinstance(e, (murphi.BooleanExpr, murphi.VarExpr, murphi.FieldName, murphi.ArrayIndex)):
            return absTransfExp(e, limits)
        else:
            raise NotImplementedError("absTransfForm on %s" % e)

    def absTransfStatement(self, cmd, limits):
        if isinstance(cmd, murphi.Skip):
            return cmd
        elif isinstance(cmd, murphi.AssignCmd):
            abs_var = absTransfVar(cmd.var, limits)
            if isinstance(abs_var, DontCareExpr):
                return murphi.Skip()
            else:
                if str(cmd.expr) in self.replacement:
                    temp_expr = self.replacement[str(cmd.expr)]
                    return murphi.AssignCmd(abs_var, temp_expr)
                else:
                    temp_expr = absTransfExp(cmd.expr, limits)
                    if isinstance(temp_expr, DontCareExpr):
                        return murphi.Skip()
                    else:
                        return murphi.AssignCmd(abs_var, temp_expr)
        elif isinstance(cmd, murphi.ForallCmd):
            # First, check for ForallExcl case
            res = check_forall_exclude_cmd(cmd)
            if res:
                excl_var, S = res
                if excl_var in limits and all(boundStatement(c, cmd.var) for c in S):
                    if limits[excl_var]:
                        return cmd
                    else:
                        return murphi.ForallCmd(cmd.var_decl, S)
                else:
                    raise NotImplementedError
            elif not all(boundStatement(c, cmd.var) for c in cmd.cmds):
                raise NotImplementedError('cmd is {}'.format(cmd))
            else:
                return cmd
        elif isinstance(cmd, murphi.IfCmd):
            # If reached this point, all if conditions must be safe.
            new_args = []
            found_cmd = False
            for cond, cmds in cmd.if_branches:
                if not safeForm(cond, limits):
                    raise NotImplementedError('cmd is {}'.format(cmd))
                new_args.append(self.absTransfForm(cond, limits))
                new_args.append(self.absTransfStatements(cmds, limits))
                if new_args[-1]:
                    found_cmd = True
            if cmd.else_branch:
                new_args.append(self.absTransfStatements(cmd.else_branch, limits))
                if new_args[-1]:
                    found_cmd = True
            if not found_cmd:
                return murphi.Skip()
            else:
                return murphi.IfCmd(new_args)
        elif isinstance(cmd, murphi.UndefineCmd):
            abs_v = absTransfVar(cmd.var, limits)
            if isinstance(abs_v, DontCareExpr):
                return murphi.Skip()
            else:
                return murphi.UndefineCmd(abs_v)
        else:
            raise NotImplementedError("absTransfStatement on %s" % cmd)

    def absTransfStatements(self, cmds, limits, repCmds = None):
        res = []
        for cmd in cmds:
            abs_cmd = self.absTransfStatement(cmd, limits)
            if not isinstance(abs_cmd, murphi.Skip):
                res.append(abs_cmd)
            if repCmds is not None and isinstance(abs_cmd, murphi.AssignCmd) and abs_cmd.expr != cmd.expr:
                repCmds[str(abs_cmd.var)] = abs_cmd.expr
        return res

    def topTransfForm(self, e, limits):
        f = self.absTransfForm(e, limits)
        # f = abs_str_Form(e, limits)
        if isinstance(f, DontCareExpr):
            return murphi.BooleanExpr(True)
        else:
            return f
        
class Replace:
    def __init__(self, dir_path, protocol_name):
        self.dirPath = dir_path
        self.protName = protocol_name
        self.protocol = parser.parse_file('{0}/{1}/{1}.m'.format(dir_path, protocol_name))
        self.repDict = dict()
        self.repProtName = '{0}/{1}/rep_{1}.m'.format(dir_path, protocol_name)
        self.absRepProtName = '{0}/{1}/ABS_rep_{1}.m'.format(dir_path, protocol_name)
        self.absProt = ''

    def needReplace(self, rulename):
        if rulename not in self.protocol.ori_rule_map:
            return False
        
        rule = self.protocol.ori_rule_map[rulename]
        assert isinstance(rule, murphi.MurphiRuleSet)
        for cmd in rule.rule.cmds:
            if not isinstance(cmd, murphi.AssignCmd):
                continue
            var, value = cmd.var, cmd.expr
            if not isinstance(value, murphi.FieldName):
                continue
            
            var_idx = re.search(r'\w+\[(.*?)\]', str(var))
            value_idx = re.search(r'\w+\[.*?\]', str(value))

            if not var_idx and value_idx:
                return True
            elif var_idx and value_idx and var_idx.group(0) != value_idx.group(0):
                return True
                
        return False

    def replace(self):
        for i, decl in enumerate(self.protocol.decls):
            if not isinstance(decl, murphi.MurphiRuleSet) or decl.rule.name not in self.repDict:
                continue

            r = self.protocol.decls[i].rule
            assert isinstance(r, murphi.MurphiRule)
            if r.name not in self.repDict:
                continue

            invs = self.repDict[r.name]
            repdict = dict()
            for inv in invs:
                content = re.findall(r'invariant.*?\n(.*?);', inv, re.S)[0]
                e = inv2OPexpr.parse_single_inv(content)
                if not isinstance(e, murphi.ForallExpr):
                    continue
                while isinstance(e, murphi.ForallExpr):
                    e = e.expr
                assert isinstance(e, murphi.OpExpr) and e.op == '->', "e.op is{}".format(e.op)
                e = e.expr2
                es = seperation(e)
                for v in es:
                    if isinstance(v, murphi.OpExpr) and v.op == '=':
                        repdict[str(v.expr1)] = v.expr2

            for i, cmd in enumerate(r.cmds):
                if not isinstance(cmd, murphi.AssignCmd) or str(cmd.expr) not in repdict:
                    continue
                r.cmds[i].expr = repdict[str(cmd.expr)]

        for i, decl in enumerate(self.absProt.decls):
            if not isinstance(decl, murphi.MurphiRuleSet) or \
                decl.rule.name not in self.repDict or \
                decl.rule.name not in self.absProt.ori_rule_map:
                continue

            r = self.absProt.decls[i].rule
            assert isinstance(r, murphi.MurphiRule)
            if r.name not in self.repDict:
                continue

            invs = self.repDict[r.name]
            repdict = dict()
            for inv in invs:
                content = re.findall(r'invariant.*?\n(.*?);', inv, re.S)[0]
                e = inv2OPexpr.parse_single_inv(content)
                if not isinstance(e, murphi.ForallExpr):
                    continue
                while isinstance(e, murphi.ForallExpr):
                    e = e.expr
                assert isinstance(e, murphi.OpExpr) and e.op == '->', "e.op is{}".format(e.op)
                e = e.expr2
                es = seperation(e)
                for v in es:
                    if isinstance(v, murphi.OpExpr) and v.op == '=':
                        repdict[str(v.expr1)] = v.expr2

            for i, cmd in enumerate(r.cmds):
                if not isinstance(cmd, murphi.AssignCmd) or str(cmd.expr) not in repdict:
                    continue
                r.cmds[i].expr = repdict[str(cmd.expr)]


    def save(self):
        with open(self.repProtName, 'w') as f:
            f.write(str(self.protocol))

        with open(self.absRepProtName, 'w') as f:
            f.write(str(self.absProt))

def absTransfRule(rule, limits, suffix=""):
    # print(rule.name, limits)
    abs_obj = Abstraction(rule, limits)
    abs_cond = abs_obj.topTransfForm(rule.cond, limits)
    abs_cmds = abs_obj.absTransfStatements(rule.cmds, limits)
    if len(abs_cmds) == 0:
        return None
    else:
        abs_name = "ABS_" + rule.name + suffix
        return murphi.MurphiRule(abs_name, abs_cond, abs_cmds)

def absStrenthfRule(rule, limits, suffix=""):
    # print('rule is {}'.format(rule))
    abs_obj = Abstraction(rule, limits)
    abs_cond = abs_obj.topTransfForm(rule.cond, limits)
    abs_cmds = abs_obj.absTransfStatements(rule.cmds, limits)
    if len(abs_cmds) == 0:
        return None
    else:
        abs_name = rule.name + suffix
        return murphi.MurphiRule(abs_name, abs_cond, abs_cmds)

def is_conj(e):
    return isinstance(e, murphi.OpExpr) and e.op == '&'

def split_conj(e):
    if is_conj(e):
        return [e.expr1] + split_conj(e.expr2)
    else:
        return [e]

def list_conj(es):
    assert len(es) > 0
    if len(es) == 1:
        return es[0]
    else:
        return murphi.OpExpr('&', es[0], list_conj(es[1:]))

def is_imp(e):
    return isinstance(e, murphi.OpExpr) and e.op == '->'

def destruct_lemma(lemma):
    if isinstance(lemma, murphi.ForallExpr):
        decls, assms, concls = destruct_lemma(lemma.expr)
        print("***{}\n***{}\n***{}".format(decls, assms, concls))
        return [lemma.var_decl] + decls, assms, concls
    elif is_imp(lemma):
        return [], split_conj(lemma.expr1), lemma.expr2

def strengthen(rule, lemma):
    _, assms, concl = destruct_lemma(lemma)
    cond_assms = split_conj(rule.cond)
    if all(assm in cond_assms for assm in assms):
        new_cond = list_conj(cond_assms + [concl])
        return murphi.MurphiRule(rule.name, new_cond, rule.cmds)
    else:
        # Should be able to strengthen
        raise NotImplementedError

def strengthen_2(rule, lemma):
    _, assms, concl = destruct_lemma(lemma)
    cond_assms = split_conj(rule.cond)
    new_cond = list_conj(cond_assms + [concl])
    return murphi.MurphiRule(rule.name, new_cond, rule.cmds)


def initAbs(filename,  output_filename=None):
    print('***Init abstract protocol {}'.format(filename))
    prot = parser.parse_file(filename)
    # print(prot)
    suffix=''
    absffix='ABS_'
    prot.abs_rule_map=dict()
    for k,r in prot.rule_map.items():
        if isinstance(r,murphi.MurphiRuleSet):
            limits=dict()
            if len(r.var_decls)==1:
                parameter_1 =  r.var_decls[0]
                if str(parameter_1.typ) != 'DATA':
                    limits[r.var_decls[0].name]=False
                    absr=absTransfRule(r.rule, limits, suffix=suffix)
                    if absr!=r.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)

            elif len(r.var_decls)==2:
                parameter_1 =  r.var_decls[0]
                parameter_2 =  r.var_decls[1]
                if str(parameter_1.typ) == 'DATA' or  str(parameter_2.typ) == 'DATA':
                    if str(parameter_1.typ) == 'NODE':
                        limits[r.var_decls[0].name]=False
                        limits[r.var_decls[1].name]=True
                        absrulesetdecls=r.var_decls[1:2]
                    elif str(parameter_2.typ) == 'NODE':
                        limits[r.var_decls[0].name]=True
                        limits[r.var_decls[1].name]=False
                        absrulesetdecls=r.var_decls[0:1]
                    else:
                        raise ValueError('rule name is {}; limits is {}'.format(str(k), limits))

                    absr=absTransfRule(r.rule, limits, suffix=suffix)
                    if absr!=None and absr != r:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map.update({absr.name:absr})
                        prot.decls.append(absruleset)
                        
                else:
                    limits[r.var_decls[0].name]=False
                    limits[r.var_decls[1].name]=True
                    absr=absTransfRule(r.rule, limits, suffix=suffix)
                    absrulesetdecls=r.var_decls[1:2]
                    if absr!=r.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)

                    limits=dict()
                    limits[r.var_decls[1].name]=False
                    limits[r.var_decls[0].name]=True
                    absr=absTransfRule(r.rule, limits, suffix=suffix)
                    absrulesetdecls=r.var_decls[0:1]
                    if absr!=r.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)

                    limits=dict()
                    limits[r.var_decls[0].name]=False
                    limits[r.var_decls[1].name]=False
                    absr=absTransfRule(r.rule, limits, suffix=suffix)
                    if absr!=r.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
        else:
             continue      

    if output_filename:
        with open(output_filename, "w") as f:
            f.write(str(prot))

def abs_strengthen(filename, output_filename=None, rulename = ''):   
    print("***you wanna abstract \"{}\"".format(filename)) 
    prot = parser.parse_file(filename)
    # print(prot)
    suffix=''
    absffix='ABS_'
    ori_abs_map = copy.deepcopy(prot.abs_rule_map)
    for k,r in ori_abs_map.items():
        if isinstance(r,murphi.MurphiRuleSet) and str(k) == rulename:
            limits=dict()
            if len(r.var_decls)==1:
                parameter_1 =  r.var_decls[0]
                if str(parameter_1.typ) != 'DATA':
                    limits[r.var_decls[0].name]=False
                    prot.decls.remove(prot.abs_rule_map[r.rule.name])
                    absr=absStrenthfRule(r.rule, limits, suffix=suffix)
                    if absr!=None and absr != r:
                        prot.decls.append(absr)
                        prot.abs_rule_map.update({absr.name:absr})

            elif len(r.var_decls)==2:
                ori_r = r
                prot.decls.remove(prot.abs_rule_map[r.rule.name])
                del(prot.abs_rule_map[r.rule.name])

                parameter_1, parameter_2 =  r.var_decls[0], r.var_decls[1]
                if str(parameter_1.typ) == 'DATA' or  str(parameter_2.typ) == 'DATA':
                    if str(parameter_1.typ) == 'NODE':
                        limits[ori_r.var_decls[0].name]=False
                        limits[ori_r.var_decls[1].name]=True
                        absrulesetdecls=r.var_decls[1:2]
                    elif str(parameter_2.typ) == 'NODE':
                        limits[ori_r.var_decls[0].name]=True
                        limits[ori_r.var_decls[1].name]=False
                        absrulesetdecls=r.var_decls[0:1]
                    else:
                        raise ValueError('rule name is {}; limits is {}'.format(rulename, limits))

                    absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                    if absr!=None and absr != r:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map.update({absr.name:absr})
                        prot.decls.append(absruleset)
                        
                else:
                    limits[ori_r.var_decls[0].name]=False
                    limits[ori_r.var_decls[1].name]=True
                    suffix = '_{}'.format(str(ori_r.var_decls[0].name))
                    absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                    absrulesetdecls=r.var_decls[1:2]
                    if absr!=None and absr != r:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map.update({absr.name:absr})
                        prot.decls.append(absruleset)

                    limits=dict()
                    limits[ori_r.var_decls[1].name]=False
                    limits[ori_r.var_decls[0].name]=True
                    suffix = '_{}'.format(str(ori_r.var_decls[1].name))
                    absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                    absrulesetdecls=ori_r.var_decls[0:1]
                    if absr!=None and absr != r:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map.update({absr.name:absr})
                        prot.decls.append(absruleset)
                        
                    limits=dict()
                    limits[r.var_decls[0].name]=False
                    limits[r.var_decls[1].name]=False
                    suffix = '_{}_{}'.format(str(ori_r.var_decls[0].name), str(ori_r.var_decls[1].name))
                    absr=absStrenthfRule(ori_r.rule, limits, suffix=suffix)
                    if absr!=None and absr != r:
                        prot.decls.append(absr)
                        prot.abs_rule_map.update({absr.name:absr})
                        
            else:
                continue      

    if output_filename:
        with open(output_filename, "w") as f:
            f.write(str(prot))

        return prot

def doMurphiCheck(name, checked):
    """cmd[0] == SET_MU_CONTEXT:
        
    In this case, cmd should be [length, command, command_id, name, context]
    """
    mu = MurphiChk(name, MU_PATH, MU_INCLUDE,  GXX_PATH, MU_FILE_DIR, 
            memory=MU_CHECK_MEMORY, timeout=MU_CHECK_TIMEOUT)
    res, checked=mu.myCheck(checked)
    # print(res)
    return res, checked

def learn_inv(flag, name, rep: Replace, log):
    print('flag is {}'.format(flag))
    log.write_log(content="rule {} need to be strengthened \n\n".format(flag))
    data_time = time.time()
    data_dir = '.'
    protocol_name = name
    processor = DataProcess(data_dir, protocol_name, replace_index=None)
    guard, para_name_dict= processor.getguard(flag)
    print("param_name_dict is {}".format(para_name_dict))
    dataset, itemMeaning = processor.exe_single(para_name_dict, guard=guard)
    global_vars = processor.select_global(itemMeaning)
    data_time_2 = time.time()
    log.write_log(content='Time spent in obtaining dataset is: {} \n\n'.format(str(data_time_2-data_time)))
    log.pre_time += data_time_2 - data_time
    
    learner = RuleLearing(data_dir, protocol_name, dataset, itemMeaning, global_vars=global_vars, max_freq_size=3,
                        min_support=0, min_confidence=1.0)
    learn_time = time.time()
    rule_tuple, rule_string_list = learner.execute(flag)
    learn_time_2 = time.time()
    print("The time spent in learning is :{}".format(str(learn_time_2 - learn_time)))
    log.write_log(content="The time spent in learning is :{} \n\n".format(str(learn_time_2 - learn_time)))
    log.learn_time += learn_time_2 - learn_time
    log.asso_num += len(rule_string_list)
    log.temp_num = len(rule_string_list)
    log.write_log(content='len of association Rules: {} \n\n'.format(len(rule_string_list)))
    
    assert len(rule_tuple) == len(rule_string_list)
    # all_types = {'NODE': 'NODENUMS'}
    prot_analyzer = Protocol(data_dir, name, '{0}/{1}/{1}.m'.format(data_dir, name))
    all_types = prot_analyzer.collect_atoms()
    instantiator = RuleLearing(data_dir, protocol_name, [], {})
    instan_rule_tuple, _ = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
    
    prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))
    select_time = time.time()
    log.temptime = select_time
    _, _ = prot_analyzer.find_rule(instan_rule_tuple, flag, boundary_K=1)
    
    #select auxiliary invariants
    suc = murphi_screen(flag, protocol_name, all_types, rep.needReplace(flag), log)
    select_time_2 = time.time()
    
    print("The time spent in selecting invariants is :{}\n\n".format(str(select_time_2 - select_time)))
    log.write_log(content="The time spent in selecting invariants is :{} \n\n".format(str(select_time_2 - select_time)))
    log.filter_time += select_time_2 - select_time
    return suc

def abs_str(flag, name, inv_num, rep: Replace, log):
    #config
    data_dir = '.'
    protocol_name = name

    #read association rules
    rule_tuple = []
    string_list = []
    rulefile = ''
    print("reading lemmas of {}".format(flag))
    with open('./{}/auxInvs/auxInvs_{}.txt'.format(protocol_name,flag), 'r') as f:
        rulefile = f.read()
    rules = list(re.findall(r'Lemma_\w+:\s*(.*?)\n', rulefile))
    for rule in rules:
        pre = rule.split('->')[0]
        conse = ' -> '.join(rule.split('->')[1:])
        conse = re.findall(r'[^()]+',conse)[0]
        if len(conse.split('->')) > 1:
            conse_1, conse_2 = conse.split('->')[0], conse.split('->')[1]
            rule_tuple.append((set(pre.split(' & ')),(set(conse_1.split(' & ')), conse_2)))
        else:
            rule_tuple.append((set(pre.split(' & ')),conse))
        string_list.append(rule)
    assert len(string_list) == len(rule_tuple) and len(string_list) != 0
    print("read success!, lemmas'len : {}".format(len(string_list)))
    rest_string_list = string_list
    assert len(rest_string_list) != 0
    if os.path.exists('./ABS{0}.m'.format(protocol_name)):
        with open('./ABS{0}.m'.format(protocol_name), 'r') as f:
            text = f.read()
            assert text != ''
    else:
        print('reading ABS_file failed!')
    prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir,  protocol_name))
    all_types = prot_analyzer.collect_atoms()

    #start strengthening
    str_time = time.time()
    str_info = ''
    pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
    rulesets = pattern.findall(text)
    for params, rules_str in rulesets:
            param_name_dict , param_name_list= analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                rulename = re.findall(r'rule\s*\"(.*?)\"\s*.*?==>.*?begin.*?endrule\s*;', each_rule, re.S)[0]
                if flag == rulename:
                    _, rev_dict = number_type(param_name_dict)
                    print("rulename is {}".format(rulename))
                    rules_str = re.sub(rulename, 'ABS_'+rulename, rules_str)
                    ruleset = 'ruleset ' + params + ' do\n' + rules_str + '\nendruleset;'
                    str_info, inv_idx, invs = inv_strengthen(rest_string_list, ruleset, all_types=all_types, NODE2para_dict=rev_dict)
                    rep.repDict[rulename] = invs
                    #end strengthening
    assert str_info != ''

    #write result
    with open("{}/{}/str_{}.m".format(data_dir, protocol_name, name), 'r') as f:
        protocol = f.read()
    with open("{}/{}/str_{}.m".format(data_dir,  protocol_name, name), 'w') as f:
        protocol_2 = re.sub(r'rule\s*"ABS_%s".*?endrule;'%flag, '', protocol, flags=re.S)
        protocol_3 = re.sub(r'ruleset.*?do\n\nendruleset;', '', protocol_2)
        f.write(protocol_3)
        f.write(str_info+'\n')
        for cnt, stmt in enumerate(rest_string_list, inv_num):
            inv_name = 'Lemma_%d'%cnt
            inv = to_murphi(inv_name, stmt, all_types, rev_dict)
            f.write(inv[0]+'\n\n')

    if os.path.exists("./ABS{}.m".format(name)):
        prot_expr = parser.parse_file("./ABS{}.m".format(name))
        with open("ABS{}.m".format(name), 'r') as f:
            protocol = f.read()
        inv_info = []
        with open("{}/ABS{}.m".format(data_dir, name), 'w') as f:
            protocol_2 = re.sub(r'rule\s*"ABS_%s".*?endrule;'%flag, '', protocol, flags=re.S)
            protocol_3 = re.sub(r'ruleset.*?do\n\nendruleset;', '', protocol_2)
            f.write(protocol_3)
            f.write(str_info+'\n')
            for stmt in rest_string_list:
                inv_name = 'Lemma_x'
                invs = to_murphi(inv_name, stmt, all_types, rev_dict, strengthen = True)
                Lemmas = ''
                for i, inv in enumerate(invs):
                    inv_expr = parser.parse_inv(inv)
                    inv_name = ''
                    for k, v in prot_expr.lemma_map.items():
                        assert isinstance(v, murphi.MurphiInvariant)
                        if str(v.inv) == str(inv_expr.inv):
                            inv_name = k
                            break

                    if inv_name == '':
                        inv_num += 1
                        inv_name = 'Lemma_{}'.format(inv_num)
                        Lemmas += inv.replace('Lemma_x', inv_name)
                        
                    inv_info.append(inv_name)
                f.write(Lemmas+'\n\n')

            #record information of strengthening
            with open("{}/{}/abs_process.csv".format(data_dir, protocol_name),"a") as f:
                f.write("{},".format(flag))
                f.write(','.join(inv_info)+'\n')

        #abstraction
        absProt = abs_strengthen("{}/ABS{}.m".format(data_dir, name), "{}/ABS{}.m".format(data_dir, name), rulename = 'ABS_{}'.format(flag))
        assert absProt != None
        rep.absProt = absProt
        str_time_2 = time.time()
        print('The time spent in strengthing {} is {}'.format(flag, str(str_time_2 - str_time)))
        log.write_log(content='The time spent in strengthing {} is {} \n\n'.format(flag, str(str_time_2 - str_time)))
        log.str_time += str_time_2 - str_time
    return inv_num

if __name__ == "__main__":
    # initAbs("./mesi/mesi.m", "./mesi/ABSmesi.m")
    # initAbs("./german/german.m", "./german/ABSgerman.m")
    # initAbs("./flash_ctc_10_origin/str_flash_ctc_10_origin.m", "./flash_ctc_10_origin/ABSstr_flash_ctc_10_origin.m")
    # initAbs("./flash/flash.m", "./ABSflash.m")
    # initAbs('./flash/str_flash.m', './tempflash.m')
    # learn_inv('NI_Remote_Get_Put', 'flash_data') 
    # inv_num = test_abs_str(flag = 'NI_Remote_GetX_Nak', name = 'flash', inv_num= 98)
    # print(inv_num)

    from process import string2tuple
    protocol_name = 'FLASHData'
    # protocol_name = 'MutualExData'
    all_types = {'NODE':'NODE_NUMS'}
    data_dir = '.'
    prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))
    flaglist = ['Store', 'NI_Remote_Get_Put', 'PI_Remote_PutX',  'NI_Remote_GetX_PutX', 'NI_Remote_GetX_Nak', 'NI_Local_GetX_PutX2', 'NI_Remote_Get_Nak', 'NI_Local_GetX_GetX', 'NI_InvAck1', 'NI_Remote_GetX_PutX_Home', 'NI_Remote_Get_Put_Home']
    # flaglist = ['NI_Remote_Get_Put']
    for flag in flaglist:
        print("reading assoRules_{}".format(flag))
        with open('./{}/assoRules/assoRules_{}.txt'.format(protocol_name,flag), 'r') as f:
            rulefile = f.read()
        rules = list(re.findall(r'rule_\w+:\s*(.*?)\n', rulefile))
        ruletuple = string2tuple(rules)
        instantiator = RuleLearing(data_dir, protocol_name, [], {})
        instan_rule_tuple, _ = instantiator.instantiate(ruletuple, rules, all_types)
        # print(ruletuple[0])
        _, _ = prot_analyzer.find_rule(instan_rule_tuple, flag, boundary_K=1)

        murphi_screen(flag, protocol_name, all_types)
