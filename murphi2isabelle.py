
from audioop import reverse
import json
#from turtle import right

import murphi
import murphiparser
import isabelle
import abstract
import lark
import copy

def translateEnum(enum_typ, enum):
    res = []
    for name in enum.names:
        res.append(isabelle.enum_def(enum_typ, name))
    return res

def translateAllEnum(prot, spec_data):
    res = []
    for item in spec_data:
        if "enum_typs" in item:
            enum_typs = item["enum_typs"]
            for enum_typ in enum_typs:
                enum = prot.enum_typ_map[enum_typ]
                res.extend(translateEnum(enum_typ, enum))
    return res

def translateBooleans():
    return [
        isabelle.Definition("true", isabelle.scalarValueType, isabelle.boolV(True), is_simp=True, is_equiv=True),
        isabelle.Definition("false", isabelle.scalarValueType, isabelle.boolV(False), is_simp=True, is_equiv=True),
    ]

def destruct_var(e, vars):
    if isinstance(e, murphi.VarExpr):
        assert e.name not in vars, "destruct_var: %s not in %s" % (e.name, vars)
        return [e.name], None
    elif isinstance(e, murphi.ArrayIndex):
        names, idx = destruct_var(e.v, vars)
        #assert idx is None and isinstance(e.idx, murphi.VarExpr) and e.idx.name in vars
        return names, e.idx.name
    elif isinstance(e, murphi.FieldName):
        names, idx = destruct_var(e.v, vars)
        return names + [e.field], idx
    else:
        # print("destruct var on %s" % e)
        raise NotImplementedError

def translateVar(v, vars):
    names, idx = destruct_var(v, vars)
    if idx is None:
        return isabelle.Ident(".".join(names))
    else:
        return isabelle.Para(".".join(names), idx)

def translateExp(e, vars):
    if isinstance(e, murphi.UnknownExpr):
        raise NotImplementedError
    elif isinstance(e, murphi.BooleanExpr):
        return isabelle.boolE(e.val)
    elif isinstance(e, murphi.EnumValExpr):
        if e.enum_val == "Other":
            return isabelle.other("N")
        else:
            return isabelle.ConstE(e.enum_val)
    elif isinstance(e, murphi.VarExpr) and e.name in vars:
        if e.typ.name == "NODE":
            return isabelle.index(e.name)
        elif e.typ.name == "DATA":
            return isabelle.data(e.name)
        
    elif isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return isabelle.IVar(translateVar(e, vars))
    else:
        # print("translateExp: %s" % e)
        raise NotImplementedError

def isGlobalVar(e,vars):

    assert(isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)))
    names, idx = destruct_var(e, vars)
    if idx is None:
        return True
    else:
        return False

def translateIsabelleExp(e, vars):
    if isinstance(e, murphi.UnknownExpr):
        raise NotImplementedError
    elif isinstance(e, murphi.BooleanExpr):
        return isabelle.boolE(e.val)
    elif isinstance(e, murphi.EnumValExpr):
        if e.enum_val == "Other":
            return isabelle.other("N")
        else:
            return isabelle.ConstE(e.enum_val)
    elif isinstance(e, murphi.VarExpr) and e.name in vars:
        return isabelle.index(e.name)
    elif isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return (translateVar(e, vars))
    else:
        # print("translateExp: %s" % e)
        raise NotImplementedError

def translateForm(e, vars):
    if isinstance(e, murphi.BooleanExpr):
        if e.val:
            return isabelle.Const("chaos")
        else:
            raise NotImplementedError
    elif isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return isabelle.eqF(isabelle.IVar(translateVar(e, vars)), isabelle.boolE(True))
    elif isinstance(e, murphi.ForallExpr):
        excl_form = abstract.check_forall_exclude_form(e)
        if excl_form:
            excl_var, concl = excl_form
            assert excl_var in vars
            vars.append(e.var)
            res = isabelle.allExclF(e.var, translateForm(concl, vars), excl_var, "N")
            del vars[-1]
            return res
        else:
            vars.append(e.var)
            res = isabelle.allF(e.var, translateForm(e.expr, vars), "N")
            del vars[-1]
            return res
    elif isinstance(e, murphi.OpExpr):
        if e.op == "=":
            return isabelle.eqF(translateExp(e.expr1, vars), translateExp(e.expr2, vars))
        elif e.op == "!=":
            return isabelle.notF(isabelle.eqF(translateExp(e.expr1, vars), translateExp(e.expr2, vars)))
        elif e.op == "&":
            return isabelle.andF([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
        elif e.op == "|":
            return isabelle.orF([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
        elif e.op == "->":
            return isabelle.impF([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
        elif e.op== "+":
            return(isabelle.addE)([translateForm(e.expr1, vars), translateForm(e.expr2, vars)])
    elif isinstance(e, murphi.NegExpr):
        if isinstance(e.expr, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
            return isabelle.eqF(isabelle.IVar(translateVar(e.expr, vars)), isabelle.boolE(False))
        else:
            return isabelle.notF(translateForm(e.expr, vars))
    else:
        # print("translateForm: %s" % e)
        raise NotImplementedError

def hasParamExpr(e):
    if isinstance(e, (murphi.VarExpr, murphi.ArrayIndex, murphi.FieldName)):
        return False
    elif isinstance(e, (murphi.UnknownExpr, murphi.BooleanExpr)):
        return False
    elif isinstance(e, murphi.EnumValExpr):
        return e.enum_val == "Other"
    elif isinstance(e, murphi.ForallExpr):
        return True
    elif isinstance(e, murphi.OpExpr):
        return hasParamExpr(e.expr1) or hasParamExpr(e.expr2)
    elif isinstance(e, murphi.NegExpr):
        return hasParamExpr(e.expr)
    else:
        # print("hasParamExpr on %s" % e)
        raise NotImplementedError

def exprHasIndex(e,idxs):
    if isinstance(e, (murphi.VarExpr)):
        if e.name in idxs:
            return([e.name])
        else:
            return([]) 
    elif isinstance(e, murphi.ArrayIndex):
        return (exprHasIndex(e.v,idxs) + exprHasIndex(e.idx,idxs))
    elif isinstance(e, murphi.FieldName):
        return exprHasIndex(e.v,idxs) 
    elif isinstance(e, (murphi.UnknownExpr, murphi.BooleanExpr)):
        return []
    elif isinstance(e, murphi.EnumValExpr):
        return []
    elif isinstance(e, murphi.ForallExpr):
        return []
    elif isinstance(e, murphi.OpExpr):
        return (exprHasIndex(e.expr1,idxs) + exprHasIndex(e.expr2,idxs))
    elif isinstance(e, murphi.NegExpr):
        return exprHasIndex(e.expr,idxs)
    else:
        # print("exprHasIndex on %s" % e)
        raise NotImplementedError

def hasParamCmd(cmd):
    if isinstance(cmd, murphi.UndefineCmd):
        return False
    elif isinstance(cmd, murphi.AssignCmd):
        return hasParamExpr(cmd.expr)
    elif isinstance(cmd, murphi.ForallCmd):
        return True
    elif isinstance(cmd, murphi.IfCmd):
        for _, cmds in cmd.if_branches:
            if any(hasParamCmd(c) for c in cmds):
                return True
        if cmd.else_branch and any(hasParamCmd(c) for c in cmd.else_branch):
            return True
        return False
    else:
        # print("hasParamCmd on %s" % cmd)
        raise NotImplementedError


def translateVar1(v, vars):
    names, idx = destruct_var(v, vars)
    if idx is None:
        # print((".".join(names))+"is global")
        return (".".join(names),None)
    else:
        return (".".join(names), idx)


class initSpec:
    def __init__(self,cmd,vars,order,defi=None):
        self.cmd=cmd 
        self.vars=vars
        self.order=order
        self.name="initSpec" + str(order)
        (str1,result)=translateVar1(self.cmd.var,vars)
        if not(result is None):
            # print("type result=\n")
            # print(type(result))
            self.assignVar=(str1)
            self.isGlobal=False 
        else:
            self.assignVar=str1
            self.isGlobal=True

        if isinstance(cmd, murphi.AssignCmd):
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = isabelle.FunType(isabelle.nat, typ)
            val = isabelle.eqF(translateExp(cmd.var, vars), translateExp(cmd.expr, vars))
            self.assignVarInIsabelle=translateExp(cmd.var, vars)
            args = []
            assert len(vars) <= 2
            for v in vars:
                if ( v.startswith('d')):
                    val = isabelle.exF(v, val, "D")
                    args.append("D")
                elif (v != "d"):
                    val = isabelle.allF(v, val, "N")
                    args.append("N")
                else:
                    raise NotImplementedError
            self.defi=(isabelle.Definition(self.name, typ, val, args=args, is_simp=True, is_equiv=True)) if defi==None else\
            defi
        elif  isinstance(cmd, murphi.UndefineCmd): 
            def_name = "initSpec" + str(order)   
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = isabelle.FunType(isabelle.nat, typ)
            assert cmd.var!= "i_0"
            val = isabelle.eqF(translateExp(cmd.var, vars), isabelle.index("i_0") )
            self.assignVarInIsabelle=translateExp(cmd.var, vars)
            args = []
            assert len(vars) <= 2
            for v in vars:
                if ( v.startswith('d')):
                    val = isabelle.allF(v, val, "D")
                    args.append("D")
                elif (v != "d"):
                    val = isabelle.allF(v, val, "N")
                    args.append("N")
                else:
                    raise NotImplementedError
            val=isabelle.exF("i_0",val,"N")
            typ = isabelle.FunType(isabelle.nat, typ) if vars==[] else typ
            if len(args)==0:
                args.append("N")  
            self.defi=(isabelle.Definition(self.name, typ, val, args=args, is_simp=True, is_equiv=True)) if defi==None else\
            defi
        print("spec export="+self.defi.export())

    
        

    def genInitSubgoalProof(self):
        args=[isabelle.Const(arg) for arg in self.defi.args]
        pred=isabelle.Fun(isabelle.Const("formEval"),[isabelle.Fun(isabelle.Const(self.defi.name),args), \
            isabelle.Const("s0")])
        
        return(isabelle.subgoaltacProof(pred))

    def __str__(self):
        return(self.name+str(self.order)+self.assignVar)
    

def translateStartState(prot):
    count = 0
    res = []
    dataRes=[]
    dataCmds=[]
    opds=[]
    initSpecs=[]
    '''lemma symPreds2 [intro]: 
  "symPredSet' N {initSpec2 D N}"
  unfolding initSpec2_def  apply(rule symPredSetExistD) 
    apply(auto intro!: equivFormAnd equivFormForall)
   
  unfolding symParamForm_def  apply(auto)
   
  done '''
    def makeSymLemma(def_name,count,args):
        predic=isabelle.Const(def_name) if args==[] else  \
            isabelle.Fun(isabelle.Const(def_name),[isabelle.Const("D"), isabelle.Const("N") ]) if "N" in args and "D" in args else \
            isabelle.Fun(isabelle.Const(def_name),[ isabelle.Const("N") ])
        proof=[isabelle.autoProof()] if args==[] else \
        [isabelle.IsabelleApplyRuleProof(name="symPredSetForall",unfolds=[def_name]),\
        isabelle.autoProof(unfolds=["symParamForm"])] if args==["N"] else\
        [isabelle.IsabelleApplyRuleProof(name="symPredSetExistD",unfolds=[def_name]),\
        isabelle.autoProof(introITag="intro!",intros=["equivFormAnd","equivFormForall"]),\
        isabelle.autoProof(unfolds=["symParamForm"])    ]
        lemma= isabelle.isabelleLemma([], isabelle.Fun(isabelle.Const("symPredSet'"), [isabelle.Const("N"),isabelle.Set(predic) ]), \
        ["intro"],"symPreds"+ str(count - 1),proof)
        return(lemma)
    
    '''lemma DsymPreds1 [intro]: 
  "DsymPredSet'  DN {initSpec1}"
  apply(rule  DsymapplyFormNone)
  unfolding initSpec1_def by auto 

  lemma DsymPreds2 [intro]: 
  "DsymPredSet'  D {initSpec2 D N}"
  
  apply(unfold initSpec2_def)
  
  apply(rule DsymPredSetExist) 
  apply(auto intro!: DsymParamFormAnd simp add: DsymParamForm_def)
  done

  
  '''
    def makeDSymLemma(def_name,count,args):
        predic=isabelle.Const(def_name) if args==[] else  \
            isabelle.Fun(isabelle.Const(def_name),[isabelle.Const("D"), isabelle.Const("N") ]) if "N" in args and "D" in args else \
            isabelle.Fun(isabelle.Const(def_name),[ isabelle.Const("N") ])
        proof=[isabelle.IsabelleApplyRuleProof(name="DsymapplyFormNone"),isabelle.autoProof()] if args==[] or args==["N"] else \
            [isabelle.IsabelleApplyRuleProof(name="DsymPredSetExist",unfolds=[def_name]),
        isabelle.autoProof(introITag="intro!",intros=["DsymParamFormAnd"],unfolds=["DsymParamForm"])]
        lemma= isabelle.isabelleLemma([], isabelle.Fun(isabelle.Const("DsymPredSet'"), [isabelle.Const("D"),isabelle.Set(predic) ]), \
        ["intro"],"DsymPreds"+ str(count - 1),proof)
        return(lemma)
                
    def translate(cmd, vars):
        nonlocal count
        if isinstance(cmd, murphi.AssignCmd):
            def_name = "initSpec" + str(count)
            typ = isabelle.formula
            noDataVars=list(filter(lambda x: x!="d",vars))
            #lenVars=len(vars) if len(vars)<2 else (len(vars) - 1 )
            for _ in range(len(noDataVars)): #len(vars)
                typ = isabelle.FunType(isabelle.nat, typ)
            val = isabelle.eqF(translateExp(cmd.var, vars), translateExp(cmd.expr, vars))
            args = []
            assert len(vars) <= 2
            for v in noDataVars:
                if ( v.startswith('d')):
                    #val = isabelle.allF(v, val, "D")
                    #args.append("D")
                    pass
                elif (v != "d"):
                    val = isabelle.allF(v, val, "N")
                    args.append("N")
                else:
                    raise NotImplementedError
            if (isinstance(cmd.expr, murphi.VarExpr) and (cmd.expr.name=="d")):
                '''deal with all data assignment'''
                dataRes.append(val) 
                dataCmds.append(cmd)
            else:
                count += 1
                #thisArgs=args[1:len(args)]
                res.append(isabelle.Definition(def_name, typ, val, args=args, is_simp=True, is_equiv=True))
                
                #predic=isabelle.Const(def_name) if args==[] else  isabelle.Fun(isabelle.Const(def_name),[isabelle.Const("N") ])
                #proof=[isabelle.autoProof()] if args==[] else [isabelle.IsabelleApplyRuleProof(name="symPredSetForall",unfolds=[def_name]),
                #isabelle.autoProof(unfolds=["symParamForm"])]
                #lemma= isabelle.isabelleLemma([], isabelle.Fun(isabelle.Const("symPredSet'"), [isabelle.Const("N"),isabelle.Set(predic) ]), \
                #["intro"],"symPreds"+ str(count - 1),proof)
                
                
                res.append(makeSymLemma(def_name,count,args)) 
                res.append(makeDSymLemma(def_name,count,args))
                setOpd = [] if args==[] else [isabelle.Const("N")]
                opd=isabelle.Set(isabelle.Fun(isabelle.Const(def_name), setOpd  ))
                opds.append(opd)
                '''f ∈ {InitSpecs_1 N} ==>deriveForm (env N) f'''
                assm=isabelle.Op(":",isabelle.Const("f"),opd)
                proof=isabelle.autoProof()
                conclusion=isabelle.Fun(isabelle.Const("deriveForm"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("f")])
                lemma=isabelle.isabelleLemma(assms=[assm],conclusion=conclusion, \
                attribs=["intro"],name="deriveFormInitSpec"+ str(count - 1),proof=[proof])
                res.append(lemma)
                thisVars=vars.copy()
                thisVars.remove("d")
                initSpecs.append(initSpec(cmd,thisVars,count - 1))

        elif isinstance(cmd, murphi.UndefineCmd):
            def_name = "initSpec" + str(count)

            count += 1
            typ = isabelle.formula
            for _ in range(len(vars)):
                typ = isabelle.FunType(isabelle.nat, typ)
            assert cmd.var!= "i_0"
            val = isabelle.eqF(translateExp(cmd.var, vars), isabelle.index("i_0") )
            args = []
            assert len(vars) <= 1
            for v in vars:
                val = isabelle.allF(v, val, "N")
                args.append("N")
            val=isabelle.exF("i_0",val,"N")
            typ = isabelle.FunType(isabelle.nat, typ) if vars==[] else typ
            if len(args)==0:
                args.append("N")  
            
            res.append(isabelle.Definition(def_name, typ, val, args=args, is_simp=True, is_equiv=True))

            '''predic=isabelle.Fun(isabelle.Const(def_name),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
            proof=[isabelle.IsabelleApplyRuleProof(name="symPredSetExist",unfolds=[def_name]),
            isabelle.autoProof(unfolds=["symParamForm"])] if vars==[] else [isabelle.IsabelleApplyRuleProof(name="symPredSetExistForall",unfolds=[def_name]),
            isabelle.autoProof(unfolds=["symParamForm2"])]
            lemma= isabelle.isabelleLemma([], isabelle.Fun(isabelle.Const("symPredSet'"), [isabelle.Const("N"),isabelle.Set(predic) ]), \
            ["intro"],"symPreds"+ str(count - 1),proof)'''
            res.append(makeSymLemma(def_name,count,args)) 
            res.append(makeDSymLemma(def_name,count,args))
            #res.append(lemma) 
                
            setOpd = [isabelle.Const("N")] #[] if args==[] else 
            opd=isabelle.Set(isabelle.Fun(isabelle.Const(def_name), setOpd  ))
            opds.append(opd) 
            '''f ∈ {InitSpecs_1 N} ==>deriveForm (env N) f'''
            assm=isabelle.Op(":",isabelle.Const("f"),opd)
            conclusion=isabelle.Fun(isabelle.Const("deriveForm"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("f")])
            proof=isabelle.autoProof()
            lemma=isabelle.isabelleLemma(assms=[assm],conclusion=conclusion, \
            attribs=["intro"],name="deriveFormInitSpec"+ str(count - 1),proof=[proof])
            res.append(lemma) 
            thisVars=vars.copy()
            thisVars.remove("d")
            initSpecs.append(initSpec(cmd,thisVars,count - 1))

        elif isinstance(cmd, murphi.ForallCmd):
            assert (cmd.typ == murphi.VarType("NODE") or cmd.typ == murphi.VarType("DATA"))
            vars.append(cmd.var)
            for c in cmd.cmds:
                translate(c, vars)
            del vars[-1]

        else:
            # print("translateStartState: %s" % cmd)
            raise NotImplementedError
    #main body    
    if isinstance(prot.start_state, murphi.MurphiRuleSet):
        tmpStartState=prot.start_state.rule
        tmpVars=list(map((lambda x: x.name),prot.start_state.var_decls))
    else:
        tmpStartState=prot.start_state.rule
        tmpVars=[]
    for cmd in tmpStartState.cmds:
        translate(cmd, tmpVars)
    
    #deal with data assignments sumUp
    if (len(tmpVars)!=0):
        valOnDataAssgn=isabelle.andF(dataRes)
        val=isabelle.exF("d",valOnDataAssgn,"D")
        count=count+1
        def_name = "initSpec" + str(count - 1)
        typ = isabelle.formula
        args = []
        args.append("D")
        args.append("N")
        typ = isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat, typ))  
        res.append(isabelle.Definition(def_name, typ, val, args=args, is_simp=True, is_equiv=True))
        setOpd =  [isabelle.Const("D"),isabelle.Const("N")]
        opd=isabelle.Set(isabelle.Fun(isabelle.Const(def_name), setOpd  ))
        #opds.append(opd)
        predic=isabelle.Const(def_name) if args==[] else  isabelle.Fun(isabelle.Const(def_name),[isabelle.Const("D"),isabelle.Const("N") ])
        proof= [isabelle.IsabelleApplyRuleProof(name="symPredSetExistD",unfolds=[def_name]),
                isabelle.autoProof(introITag="intro!",intros=["equivFormAnd","equivFormForall"]),
                isabelle.autoProof(unfolds=["symParamForm"])]
        lemma= isabelle.isabelleLemma([], isabelle.Fun(isabelle.Const("symPredSet'"), [isabelle.Const("N"),isabelle.Set(predic) ]), \
                ["intro"],"symPreds"+ str(count - 1),proof)
        #res.append(lemma) 
        res.append(makeSymLemma(def_name,count,args)) 
        res.append(makeDSymLemma(def_name,count,args))
        setOpd = [] if args==[] else [isabelle.Const("D"), isabelle.Const("N")]
        opd=isabelle.Set(isabelle.Fun(isabelle.Const(def_name), setOpd  ))
        opds.append(opd)
        '''f ∈ {InitSpecs_1 N} ==>deriveForm (env N) f'''
        assm=isabelle.Op(":",isabelle.Const("f"),opd)
        proof=isabelle.autoProof()
        conclusion=isabelle.Fun(isabelle.Const("deriveForm"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("f")])
        lemma=isabelle.isabelleLemma(assms=[assm],conclusion=conclusion, \
        attribs=["intro"],name="deriveFormInitSpec"+ str(count - 1),proof=[proof])
        res.append(lemma)
        defiOnd=isabelle.Definition(def_name, typ, val, args=args, is_simp=True, is_equiv=True)
        for cmd0 in dataCmds:
            initSpecs.append(initSpec(cmd0,tmpVars,count - 1,defiOnd))
        
    else:
        pass    
    val=isabelle.UN(opds)
    allSpec=isabelle.Definition("allInitSpecs", isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.formula)), val, args=["N"], is_simp=True, is_equiv=True) if (len(tmpVars)==0) else \
    isabelle.Definition("allInitSpecs", isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.formula))), val, args=["D","N"], is_simp=True, is_equiv=True)  
    res.append(allSpec)
    proofs=[]
    for k  in range(len(opds)-1):
        proofs.append(isabelle.IsabelleApplyRuleProof(name="symPredsUnion",unfolds= ["allInitSpecs"]))
        proofs.append(isabelle.blastProof())
    theLast=isabelle.blastProof() if (len(opds)>1) else isabelle.blastProof(unfolds=["allInitSpecs"])
    lemma=isabelle.isabelleLemma([], 
        isabelle.Fun(isabelle.Const("symPredSet'"), [isabelle.Const("N"), isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("N")])]),
        ["intro"],
        "symPreds",
        proofs+[theLast]
    )
    res.append(lemma)
    proofs=[]
    for k  in range(len(opds)-1):
        proofs.append(isabelle.IsabelleApplyRuleProof(name="DsymPredsUnion",unfolds= ["allInitSpecs"]))
        proofs.append(isabelle.blastProof())
    theLast=isabelle.blastProof() if (len(opds)>1) else isabelle.blastProof(unfolds=["allInitSpecs"])
    lemma=isabelle.isabelleLemma([], 
        isabelle.Fun(isabelle.Const("DsymPredSet'"), [isabelle.Const("N"), isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("N")])]),
        ["intro"],
        "DsymPreds",
        proofs+[theLast]
    )
    assm=isabelle.Op(":",isabelle.Const("f"),isabelle.Fun(isabelle.Const("allInitSpecs"), [isabelle.Const("D"),isabelle.Const("N")]))
    conclusion=isabelle.Fun(isabelle.Const("deriveForm"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("f")])
    
    usings=["deriveFormInitSpec"+str(k) for k in range(0,count )]
    simpdels=["initSpec"+ str(k) +"_def" for k in range(0,count )]
    proof=isabelle.autoProof(usings=usings,simpdels=simpdels)
    lemma=isabelle.isabelleLemma(assms=[assm], conclusion=conclusion, \
        proof=[proof],name="deriveFormAllInitSpec")
    res.append(lemma)
    return (res,initSpecs)

'''def translateEnv(prot):
    eqs=[]
    for var_decl in prot.vars:
        if var_decl.typ
        self.var_map[var_decl.name] = var_decl.typ'''


#generate environment definitions, and lemmas, declarations
def translateEnvByStartState(prot):
    eqIdents=[]
    eqParas=[]
    cmpPara=isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("n"),isabelle.Const("i")])
    cmpIdent=isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("n")])
    identLemmas=[]
    paraLemmas=[]
    para=""

    def makeite(isIdentOrPara="isIdent"):
        if isIdentOrPara=="isIdent":
            if(eqIdents!=[]):
                left,right=eqIdents[0]
                del(eqIdents[0])
                eq=isabelle.eq(cmpIdent,left)
                
                return(isabelle.IsabelleITE("isabelleIte",eq,right,makeite("isIdent")))
            else:
                return(isabelle.Const("anyType"))
        else:
            if(eqParas!=[]):
                left,right=eqParas[0]
                del(eqParas[0])
                eq=isabelle.eq(cmpPara,left)
                eq1=isabelle.Op("<=",isabelle.Const(para),isabelle.Const("N"))
                cond=isabelle.Op("&",eq,eq1)
                return(isabelle.IsabelleITE("isabelleIte",cond,right,makeite("isPara")))
            else:
                return(isabelle.Const("anyType"))

    def makeSimpLemmasOn(i,isIdentOrPara="isIdent"):
        if isIdentOrPara=="isIdent":
            if (i==len(eqIdents)):
                pass
            else:
                left,right=eqIdents[i]
                left1=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N"),left])
                eq=isabelle.eq(left1,right)
                identLemmas.append(isabelle.isabelleLemma(assms=[], conclusion=eq,inLemmas=True))
                makeSimpLemmasOn(i+1,"isIdent")
        else:
            if (i==len(eqParas)):
                pass
            else:
                left,right=eqParas[i]
                left2=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N"),left])
                eq1=isabelle.eq(left2,right)
                cond1=isabelle.Op("<=",isabelle.Const(para),isabelle.Const("N"))
                paraLemmas.append(isabelle.isabelleLemma(assms=[cond1], conclusion=eq1,inLemmas=True))
                #eq2=isabelle.eq(cmpPara,left)
                #cond2=isabelle.Op(">",isabelle.Const("i"),isabelle.Const("N"))
                #paraLemmas.append(isabelle.isabelleLemma(assms=[cond2], conclusion=eq2,inLemmas=True))
                makeSimpLemmasOn(i+1,"isPara")

    def hasArrayIndex(v):
        if isinstance(v,murphi.VarExpr):
            return(False)
        else:
            if isinstance(v,murphi.ArrayIndex):
                return(True)
            else:
                if isinstance(v,murphi.FieldName):
                    return(hasArrayIndex(v.field) or hasArrayIndex(v.v))
                
                else:
                    if isinstance(v,lark.lexer.Token):
                        return(False)
                    else:
                        #print(type(v))
                        raise NotADirectoryError

    def translate(cmd, vars):
        nonlocal para
        if isinstance(cmd, murphi.AssignCmd):
            varOpd=translateIsabelleExp(cmd.var, vars)
            
            typ=isabelle.Const("enumType") if isinstance(cmd.expr,murphi.EnumValExpr) else \
                isabelle.Const("boolType") if isinstance(cmd.expr,murphi.BooleanExpr) else \
                isabelle.Const("indexType") if isinstance(cmd.expr,murphi.VarExpr) and (cmd.expr.typ.name=="NODE") else \
                isabelle.Const("dataType")
            val=(varOpd,typ)
            #print(type(cmd.var))
            if hasArrayIndex(cmd.var):
                eqParas.append(val)
            else:
                eqIdents.append(val)

        elif isinstance(cmd, murphi.UndefineCmd):
            varOpd=translateIsabelleExp(cmd.var, vars)
            typ=isabelle.Const("indexType") 
            val =(varOpd,typ)
            if hasArrayIndex(cmd.var):
                eqParas.append(val)
            else:
                eqIdents.append(val)

        elif isinstance(cmd, murphi.ForallCmd):
            assert (cmd.typ == murphi.VarType("NODE") or  cmd.typ == murphi.VarType("DATA"))
            vars.append(cmd.var)
            para=cmd.var
            for c in cmd.cmds:
                translate(c, vars)
            del vars[-1]

        else:
            # print("translateStartState: %s" % cmd)
            raise NotImplementedError

    print(prot.start_state.__str__())
    if isinstance(prot.start_state, murphi.MurphiRuleSet):
        tmpStartState=prot.start_state.rule
        tmpVars=prot.start_state.var_decls
    else:
        tmpStartState=prot.start_state.rule
        tmpVars=[]
    for cmd in tmpStartState.cmds:
        translate(cmd, [])

    cmpPara=isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("n"),isabelle.Const(para)])
    cmpIdent=isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("n")])
    tmp=makeSimpLemmasOn(0,"isIdent")
    tmp=makeSimpLemmasOn(0,"isPara")
             
    paraLemmas.extend(identLemmas)  
    
    left2=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N"),cmpPara])
    eq2=isabelle.eq(left2,isabelle.Const("anyType"))
    cond2=isabelle.Op(">",isabelle.Const(para),isabelle.Const("N"))
    paraLemmas.append(isabelle.isabelleLemma(assms=[cond2], conclusion=eq2,inLemmas=True))
    
    '''for k in eqParas:
        (varOpdk, typk)=k
        print("this para[k]%s,typ"%str(varOpdk),str(typk))
    for k in eqIdents:
        (varOpdk, typk)=k
        print("this eqIdent[k]%s,typ"%str(varOpdk),str(typk))'''
    primTyp=isabelle.FunType(isabelle.nat,isabelle.ConstType("envType"))
    left1=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N"),cmpIdent])
    eq1=isabelle.eq(left1,makeite("isIdent"))
    left2=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N"),cmpPara])
    eq2=isabelle.eq(left2,makeite("isPara"))
    dontCareVarExp=isabelle.Const("dontCareVar")
    left3=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N"),dontCareVarExp])
    eq3=isabelle.eq(left3,isabelle.Const("anyType"))
    primrec=isabelle.primRec("env",primTyp,[eq1,eq2,eq3])
    res=[]
    
    proof=isabelle.autoProof()
    lemmas=isabelle.isabelleLemmas(name="env_simp",lemmas=paraLemmas,proof=[proof])
    
    res.append(primrec)
    res.append(lemmas)
    return res

def check_ite_assign_cmd(c):
    """If c is of the form if b then v := e1 else v := e2 end,
    return (b, v, e1, e2). Otherwise, return None.
    
    """
    if isinstance(c, murphi.IfCmd):
        if len(c.if_branches) == 1 and c.else_branch is not None:
            cond, if_cmds = c.if_branches[0]
            if len(if_cmds) == 1 and len(c.else_branch) == 1:
                c1, c2 = if_cmds[0], c.else_branch[0]
                if isinstance(c1, murphi.AssignCmd) and isinstance(c2, murphi.AssignCmd) and \
                    c1.var == c2.var:
                    return (cond, c1.var, c1.expr, c2.expr)

def translateCmd(cmd, vars):
    if isinstance(cmd, murphi.Skip):
        return isabelle.Const("skip")
    elif isinstance(cmd, murphi.AssignCmd):
        return isabelle.assignS(translateVar(cmd.var, vars), translateExp(cmd.expr, vars))
    elif isinstance(cmd, murphi.UndefineCmd):
        return None
    elif isinstance(cmd, murphi.ForallCmd):
        excl_form = abstract.check_forall_exclude_cmd(cmd)
        if excl_form:
            excl_var, concl = excl_form
            assert excl_var in vars
            vars.append(cmd.var)
            res = isabelle.forallExclS(cmd.var, translateCmds(concl, vars), excl_var, "N")
            del vars[-1]
            return res
        else:
            vars.append(cmd.var)
            res = isabelle.forallS(cmd.var, translateCmds(cmd.cmds, vars), "N")
            del vars[-1]
            return res
    elif isinstance(cmd, murphi.IfCmd):
        ite_assign_form = check_ite_assign_cmd(cmd)
        if ite_assign_form:
            cond, var, s1, s2 = ite_assign_form
            res = isabelle.assignS(translateVar(var, vars), isabelle.iteF(translateForm(cond, vars), translateExp(s1, vars), translateExp(s2, vars)))
            return res
        else:
            cond, c1 = cmd.if_branches[0]
            if len(cmd.if_branches) == 1:
                if cmd.else_branch:
                    isa_c2 = translateCmds(cmd.else_branch, vars)
                else:
                    isa_c2 = translateCmd(murphi.Skip(), vars)
            else:
                isa_c2 = translateCmd(murphi.IfCmd(cmd.args[2:]), vars)
            return isabelle.ITE("iteStm", translateForm(cond, vars), translateCmds(c1, vars), isa_c2)
    else:
        # print("translateCmd: %s" % cmd)
        raise NotImplementedError
    
def translateCmds(cmds, vars):
    isa_cmds = []
    for cmd in cmds:
        isa_cmd = translateCmd(cmd, vars)
        if isa_cmd is not None:
            isa_cmds.append(isa_cmd)
    return isabelle.parallelS(isa_cmds)

def translateRuleTerm(rule, vars):
    isa_cond = translateForm(rule.cond, vars)
    isa_cmds = translateCmds(rule.cmds, vars)
    return isabelle.Op("|>", isa_cond, isa_cmds)

def translateRule(rule):
    isa_rule = translateRuleTerm(rule, [])
    typ = isabelle.rule
    args = []
    if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
        typ = isabelle.FunType(isabelle.nat, typ)
        args.append("N")
    return isabelle.Definition(rule.name, typ, isa_rule, args=args, is_equiv=True)

def translateRuleSet(ruleset):
    typ = isabelle.rule
    vars = []
    if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
        typ = isabelle.FunType(isabelle.nat, typ)
        vars.append("N")
    decls=sorted(ruleset.var_decls, key=lambda x: x.name)
    for var_decl in decls:
        typ = isabelle.FunType(isabelle.nat, typ)
        vars.append(var_decl.name)
        #print(var_decl.name)
        #print("88")    
    '''for var_decl in ruleset.var_decls:
        typ = isabelle.FunType(isabelle.nat, typ)
        vars.append(var_decl.name)'''
    isa_rule = translateRuleTerm(ruleset.rule, vars)
    return isabelle.Definition(ruleset.rule.name, typ, isa_rule, args=vars, is_equiv=True)



#generate def of rs, and  lemma items on deriveRule, symProts, and terms rs N  in rules--such as Trys
#deriveAll lemmas such as r ∈ Trys N ⟹ deriveRule (env N) r
'''definition Trys :: "nat \<Rightarrow> rule set" where
  "Trys N \<equiv> oneParamCons N Try"
  definition NI_Remote_Get_Put_refs :: "nat \<Rightarrow> rule set" where [rules_simp]:
  "NI_Remote_Get_Put_refs N \<equiv> twoParamsCons N (NI_Remote_Get_Put_ref N)
 
lemma deriveAll:
  "r \<in> Trys N \<Longrightarrow> deriveRule (env N) r"
  "r \<in> Crits N \<Longrightarrow> deriveRule (env N) r"
  "r \<in> Exits N \<Longrightarrow> deriveRule (env N) r"
  "r \<in> Idles N \<Longrightarrow> deriveRule (env N) r"
  by (auto simp: deriveRule_def deriveForm_def deriveStmt_def
      Trys_def Try_def Crits_def Crit_def Exits_def Exit_def Idles_def Idle_def)

lemma symProtAll:
  "symProtRules' N (Trys N)"
  "symProtRules' N (Crits N)"
  "symProtRules' N (Exits N)"
  "symProtRules' N (Idles N)"
  using symTry(1) Trys_def symCrit(1) Crits_def symExit(1) Exits_def
    symIdle(1) Idles_def
    symParaRuleInfSymRuleSet by auto 

definition rules :: "nat \<Rightarrow> rule set" where
  "rules N \<equiv> Trys N \<union> Crits N \<union> Exits N \<union> Idles N"

  "'''

def translateRuleSets(ruleset):
    
    vars = []
    # print(ruleset.rule.name+"'paras ="+str(ruleset.var_decls))
    if "N" in (decl.name for decl in ruleset.var_decls):
        pass
    else:
        if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
            #typ = isabelle.FunType(isabelle.nat, typ)
            vars.append("N")
    for var_decl in ruleset.var_decls:
        #typ = isabelle.FunType(isabelle.nat, typ)
        vars.append(var_decl.name)
    #isa_rule = translateRuleTerm(ruleset.rule, vars)
    # print("vars ="+str(vars))
    if ("N" in vars):
        count=len(vars) - 1
    else:
        count=len(vars)

    typ = isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule))
    NParam=isabelle.Const("N")
    ruleParam=isabelle.Fun(isabelle.Const(ruleset.rule.name),[NParam]) if ("N" in vars) \
        else isabelle.Const(ruleset.rule.name)
    if count==1:
        if (not("d" in  vars)):
            isa_rule=isabelle.Fun(isabelle.Const("oneParamCons"),[isabelle.Const("N"),ruleParam])
            args=["N"]
        else:
            isa_rule=isabelle.Fun(isabelle.Const("oneParamCons"),[isabelle.Const("D"),ruleParam])
            args=["D","N"]
            typ = isabelle.FunType(isabelle.nat,typ)
    elif (count==2 and "d" in vars):
        isa_rule=isabelle.Fun(isabelle.Const("twoDIParamsCons"),[isabelle.Const("D"),isabelle.Const("N"),ruleParam])
        typ = isabelle.FunType(isabelle.nat,typ)
        args=["D","N"]
    else:
        isa_rule=isabelle.Fun(isabelle.Const("twoParamsCons"),[isabelle.Const("N"),ruleParam])
        args=["N"]
    def1=isabelle.Definition(ruleset.rule.name+"s", typ, isa_rule, args=args, is_equiv=True)
    print("---in translateRuleSets----")
    print(def1.export())
    assm1=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),\
        list(map(lambda x: isabelle.Const(x),args))))
    cons1=isabelle.Fun(isabelle.Const("deriveRule"), \
    [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),isabelle.Const("r")])
    lemma1=isabelle.isabelleLemma(assms=[assm1],conclusion=cons1,inLemmas=True)
    unfolds1=[ruleset.rule.name+"s",ruleset.rule.name]
    usings2=["sym"+ruleset.rule.name+"(1)",ruleset.rule.name+"s_def"]

    cons2=isabelle.Fun(isabelle.Const("symProtRules'"),[isabelle.Const("N"), \
        isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),[isabelle.Const("N")])]) if args==["N"] else\
        isabelle.Fun(isabelle.Const("symProtRules'"),[isabelle.Const("N"), \
        isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),[isabelle.Const("D"),isabelle.Const("N")])])
    dcons2=isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"), \
        isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),[isabelle.Const("N")])]) if args==["N"] else\
        isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"), \
        isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),[isabelle.Const("D"),isabelle.Const("N")])])
    
    lemma2=isabelle.isabelleLemma(assms=[],conclusion=cons2,inLemmas=True)
    dlemma2=isabelle.isabelleLemma(assms=[],conclusion=dcons2,inLemmas=True)
    term=isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),[isabelle.Const("N")]) if not(count==2 and "d" in vars) else\
        isabelle.Fun(isabelle.Const(ruleset.rule.name+"s"),[isabelle.Const("D"),isabelle.Const("N")])

    return (def1,lemma1,lemma2,dlemma2,term,unfolds1,usings2)

def translateRule1(rule):
    
    vars = []
    #print(rule.name+"'paras ="+str(var_decls))
    if "N" in []: #(decl.name for decl in ruleset.var_decls):
        pass
    else:
        if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
            #typ = isabelle.FunType(isabelle.nat, typ)
            vars.append("N")
    '''for var_decl in ruleset.var_decls:
        #typ = isabelle.FunType(isabelle.nat, typ)
        vars.append(var_decl.name)'''
    #isa_rule = translateRuleTerm(ruleset.rule, vars)
    # print("vars ="+str(vars))
    if ("N" in vars):
        count=len(vars) - 1
    else:
        count=len(vars)

    typ = isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule)) if ("N" in vars) else isabelle.setType(isabelle.rule)
    NParam=isabelle.Const("N")
    ruleParam=isabelle.Fun(isabelle.Const(rule.name),[NParam]) if ("N" in vars) else isabelle.Const(rule.name)
    '''if count==1:
        isa_rule=isabelle.Fun(isabelle.Const("oneParamCons"),[isabelle.Const("N"),ruleParam])
    else:
        isa_rule=isabelle.Fun(isabelle.Const("twoParamsCons"),[isabelle.Const("N"),ruleParam])'''
    isa_rule=isabelle.Set(isabelle.Const(rule.name))
    def1=isabelle.Definition(rule.name+"s", typ, isabelle.Set(ruleParam), args=vars, is_equiv=True)
    # print(def1.export())
    opds=[isabelle.Const(n) for n in vars]
    assm1=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const(rule.name+"s"),opds))
    cons1=isabelle.Fun(isabelle.Const("deriveRule"), \
    [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),isabelle.Const("r")])
    lemma1=isabelle.isabelleLemma(assms=[assm1],conclusion=cons1,inLemmas=True)
    unfolds1=[rule.name+"s",rule.name]
    usings2=["sym"+rule.name+"(1)", rule.name+"s_def"]

    cons2=isabelle.Fun(isabelle.Const("symProtRules'"),[isabelle.Const("N"), \
        isabelle.Fun(isabelle.Const(rule.name+"s"),opds)])
    dcons2=isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"), \
        isabelle.Fun(isabelle.Const(rule.name+"s"),opds)])
    lemma2=isabelle.isabelleLemma(assms=[],conclusion=cons2,inLemmas=True)
    dlemma2=isabelle.isabelleLemma(assms=[],conclusion=dcons2,inLemmas=True)
    term=isabelle.Fun(isabelle.Const(rule.name+"s"),opds)

    return (def1,lemma1,lemma2,dlemma2,term,unfolds1,usings2)


def translateInvariant(inv):
    typ = isabelle.formula
    args = []
    if hasParamExpr(inv.inv):
        typ = isabelle.FunType(isabelle.nat, typ)
        args.append("N")
    # Extract two parameters
    inv_t = inv.inv
    print("inv_t:"+(inv_t.__str__()))
    for _ in range(2):
        
        assert isinstance(inv_t, murphi.ForallExpr)
        typ = isabelle.FunType(isabelle.nat, typ)
        args.append(inv_t.var)
        inv_t = inv_t.expr
    isa_inv = translateForm(inv_t, args)
    excl_form = abstract.check_forall_exclude_form(inv_t.expr2)
    if excl_form:
        isa_inv = translateForm(inv_t, args) 
    else:
        if isinstance(inv_t.expr2 , murphi.OpExpr) and (inv_t.expr2.op=="=") and (inv_t.expr2.expr2.typ.name=="DATA"):
            args.append("d")
            args=[item for item in args if item!= "N" and item!= "m"]
            args=sorted(args, key=lambda x:x[0])
            isa_inv = translateForm(inv_t, args)
            typ=typ.range
            #vars.append(e.var)
        else:
            isa_inv = translateForm(inv_t, args)   
    return isabelle.Definition(inv.name, typ, isa_inv, args=args, is_equiv=True)

#  lemma symNI_Local_PutXAcksDone:
# "wellFormedRule (env N) N NI_Local_PutXAcksDone"
# unfolding NI_Local_PutXAcksDone_def by auto


def genRuleSetSymLemma(ruleset):
    vars = []
    hasForall=False
    if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
        vars.append("N")
        hasForall=True
    decls=sorted(ruleset.var_decls, key=lambda x: x.name)
    for var_decl in decls:
        vars.append(var_decl.name)
        #print(var_decl.name)
        #print("88")
    paraNums=len(vars) - 1 if hasForall else len(vars)
    args=list(map(lambda a: isabelle.Const(a),vars))
    ruleConst=isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N")]) if hasForall and not("d" in vars) else\
        isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N"),isabelle.Const("d")]) if hasForall and  ("d" in vars) else\
        isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("d")]) if ("d" in vars) else\
        isabelle.Const(ruleset.rule.name)
    ruleInst=isabelle.Fun(isabelle.Const(ruleset.rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
    predic1=isabelle.Fun(isabelle.Const("symParamRule"),[isabelle.Const("N"),ruleConst]) if paraNums==1 else\
        isabelle.Fun(isabelle.Const("symParamRule2'"),[isabelle.Const("N"),ruleConst]) if paraNums==2 and not("d" in vars) else\
        isabelle.Fun(isabelle.Const("symParamRule"),[isabelle.Const("N"),ruleConst])
    lemma1= isabelle.isabelleLemma(assms=[], conclusion=predic1,inLemmas=True)
    env=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
    predic2=isabelle.Fun(isabelle.Const("wellFormedRule"),[env,isabelle.Const("N"),ruleInst])
    tmpVars0=(filter(lambda x:x.name!="d",ruleset.var_decls))
    assms=[isabelle.Op("<=",isabelle.Const(n.name),isabelle.Const("N")) for n in  tmpVars0]
    lemma2= isabelle.isabelleLemma(assms=assms, conclusion=predic2,inLemmas=True)
    intros=["symParamRuleI2","symParamRuleI","symParamFormAnd","symParamFormForall", \
     "symParamFormForallExcl", "symParamFormImply" ,"symParamStatementParallel","symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte"] if (paraNums==1 or (paraNums==2 and "d" in vars)) else \
         ["symParamRuleI2", "symParamRuleI", "symParamForm2And", "symParamForm2Forall1", "symParamForm2Forall2", "symParamFormForallExcl1","symParamFormForallExcl2", "symParamForm2Imply", \
              "symParamStatementParallel", "symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte" ]      
 
    proof1=isabelle.autoProof(unfolds=[ruleset.rule.name],introITag="intro!",intros=intros)
    proof2=isabelle.autoProof(unfolds=["symParamForm_def  symParamStatement_def \
    symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm"])
    lemmas= isabelle.isabelleLemmas(name="sym"+ruleset.rule.name,lemmas=[lemma1,lemma2],proof=[proof1,proof2])
    return lemmas 


def genRuleSetDSymLemma(ruleset):
    vars = []
    hasForall=False
    if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
        vars.append("N")
        hasForall=True

    for var_decl in ruleset.var_decls:
        vars.append(var_decl.name)
    paraNums=len(vars) - 1 if hasForall else len(vars)
    args=list(map(lambda a: isabelle.Const(a),vars))
    '''ruleConst=isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N")]) if hasForall else\
        isabelle.Const(ruleset.rule.name)'''
    if not(ruleset.rule.name.startswith("ABS")): 
        ruleConst=isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N"),isabelle.Const("i")]) if hasForall and not("d" in vars) else\
        isabelle.Quant("%","d",isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N"),isabelle.Const("d"),isabelle.Const("i")])) if hasForall and  ("d" in vars) else\
        isabelle.Quant("%","d",isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("d"),isabelle.Const("i")])) if ("d" in vars)  else\
        isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("i")])  
    else:
        ruleConst=isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N")]) if hasForall and not("d" in vars) else\
        isabelle.Quant("%","d",isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N"),isabelle.Const("d") ]))  

    ruleInst=isabelle.Fun(isabelle.Const(ruleset.rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
    predic1=isabelle.Fun(isabelle.Const("DsymapplyRuleNothing"),[ruleConst]) if paraNums==1 and not("d" in vars)else\
        isabelle.Fun(isabelle.Const("symParamRule2'"),[isabelle.Const("N"),ruleConst]) if paraNums==2 and not("d" in vars) else\
        isabelle.Fun(isabelle.Const("DsymParamRule"),[isabelle.Const("D"),ruleConst])
    '''predic1=isabelle.Fun(isabelle.Const("DsymParamRule"),[isabelle.Const("D"),ruleConst]) if paraNums==1 else\
        isabelle.Fun(isabelle.Const("symParamRule2'"),[isabelle.Const("N"),ruleConst])'''
    lemma1= isabelle.isabelleLemma(assms=[], conclusion=predic1,inLemmas=True)
    env=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
    predic2=isabelle.Fun(isabelle.Const("wellFormedRule"),[env,isabelle.Const("N"),ruleInst])
    tmpVars0=(filter(lambda x:x.name!="d",ruleset.var_decls))
    assms=[isabelle.Op("<=",isabelle.Const(n.name),isabelle.Const("N")) for n in  tmpVars0]
    lemma2= isabelle.isabelleLemma(assms=assms, conclusion=predic2,inLemmas=True)
    intros=["symParamRuleI2","symParamRuleI","symParamFormAnd","symParamFormForall", \
     "symParamFormForallExcl", "symParamFormImply" ,"symParamStatementParallel","symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte"] if (paraNums==1 or (paraNums==2 and "d" in vars)) else \
         ["symParamRuleI2", "symParamRuleI", "symParamForm2And", "symParamForm2Forall1", "symParamForm2Forall2", "symParamFormForallExcl1","symParamFormForallExcl2", "symParamForm2Imply", \
              "symParamStatementParallel", "symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte" ]      
 
    proof1=isabelle.autoProof(unfolds=[ruleset.rule.name,"DsymapplyRuleNothing","DsymParamRule"])
    proof2=isabelle.autoProof(unfolds=["DsymParamForm_def  DsymParamStatement_def \
    DsymParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm"])
    lemmas= isabelle.isabelleLemmas(name="Dsym"+ruleset.rule.name,lemmas=[lemma1],proof=[proof1])
    return lemmas 
#unfolds=[], usings=[], introITag=None,
#        intros=[],destITag=None,dests=[],simpadds=[], simpdels=[],plus=None
#        lemma symIdle_ref:
#  "symParamRule N (Idle_ref N)"
#  "wellFormedRule (env N) N (Idle_ref N i)"
#  unfolding Idle_ref_def
#   apply (auto intro!: symParamRuleI symParamFormAnd symParamFormForall
#      symParamFormForallExcl symParamStatementParallel symParamStatementForall symParamStatementForallExcl)
#  unfolding symParamForm_def symParamForm_def symParamStatement_def
#    symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm_def by auto   

def makeSymProtAllProof(usings):
    i=0
    proofs=[]
    while i< len(usings):
        thisUsings=[usings[i],usings[i+1],"symParaRuleInfSymRuleSet", "symParaRuleInfSymRuleSet2"]
        proofs.append(isabelle.autoProof(usings=thisUsings,goalNum="1"))
        i=i+2
    return proofs

def translateAllSpecs(prot):
    def makeRulesDef(rulesDefList,args):
        typ = isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule)) if args==["N"] else\
        isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule)))
        def_rules=isabelle.Definition(name="rules",typ=typ,val=isabelle.UN(rulesDefList),args=args)
        return(def_rules)
    res = []
    rulesDefList=[]
    deriveAllLLemmaist=[]
    symProtAllLemmaList=[]
    dsymProtAllLemmaList=[]
    deriveAllLLemmaProofUnfolds1=[]
    symProtAllLemmaProofUsings2=[]
    doccurs=False
    
    for decl in prot.decls:
        if isinstance(decl, murphi.MurphiRule):
            res.append(translateRule(decl))
            if True: #(decl in prot.ori_rule_map.values()):
                if (decl in prot.abs_rule_map.values()):
                    res.append(genRuleDSymLemma(decl))
                else:
                    res.append(genRuleSymLemma(decl))
                '''if (decl not in prot.abs_rule_map.values()):
                    res.append(genRuleSymLemma(decl))'''
                def1,lemma1,lemma2,dlemma2,term1,unfolds,usings=translateRule1(decl)
                res.append(def1)
                deriveAllLLemmaist.append(lemma1)
                if (decl in prot.ori_rule_map.values()):
                    symProtAllLemmaList.append(lemma2)
                    dsymProtAllLemmaList.append(dlemma2)
                    rulesDefList.append(term1)
                deriveAllLLemmaProofUnfolds1.extend(unfolds)
                if (decl in prot.ori_rule_map.values()):
                    symProtAllLemmaProofUsings2.extend(usings)


        elif isinstance(decl, murphi.MurphiRuleSet):
            res.append(translateRuleSet(decl))
            doccurs=True if "d" in map(lambda x: x.name, decl.var_decls) else doccurs
            if True: #(decl in prot.ori_rule_map.values()):
                if (decl not in prot.abs_rule_map.values()):
                    res.append(genRuleSetSymLemma(decl)) 
                    res.append(genRuleSetDSymLemma(decl)) 
                else:
                    if doccurs:
                        #res.append(genRuleSetSymLemma(decl)) 
                        res.append(genRuleSetDSymLemma(decl))    
                    else:
                        #res.append(genRuleSymLemma(decl))
                        res.append(genRuleDSymLemma(decl))
                #res.append(genRuleSetSymLemma(decl))
                #res.append(genRuleSetDSymLemma(decl))
                def1,lemma1,lemma2,dlemma2,term1,unfolds,usings=translateRuleSets(decl)
                #rulesDefList.append(term1)
                res.append(def1)
                #if (decl in prot.ori_rule_map.values()):
                deriveAllLLemmaist.append(lemma1)
                if (decl in prot.ori_rule_map.values()):    
                    symProtAllLemmaList.append(lemma2)
                    dsymProtAllLemmaList.append(dlemma2)
                    rulesDefList.append(term1)
                deriveAllLLemmaProofUnfolds1.extend(unfolds)
                if (decl in prot.ori_rule_map.values()):
                    symProtAllLemmaProofUsings2.extend(usings)

        elif isinstance(decl, murphi.MurphiInvariant):
            res.append(translateInvariant(decl))
    #typ = isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule))
    #def_rules=isabelle.Definition(name="rules",typ=typ,val=isabelle.UN(rulesDefList),args=["N"])
    print(doccurs)
    args=["N"] if (not(doccurs)) else ["D","N"]
    res.append(makeRulesDef(rulesDefList,args))
    deriveAllLLemmaProof=[isabelle.autoProof(unfolds=["deriveRule_def deriveForm_def deriveStmt"] \
        +deriveAllLLemmaProofUnfolds1)]
    symProtAllLemmaProof=makeSymProtAllProof(symProtAllLemmaProofUsings2)
    #[isabelle.autoProof(usings=symProtAllLemmaProofUsings2+["symParaRuleInfSymRuleSet","symParaRuleInfSymRuleSet2"])]
    deriveAllLLemmas=isabelle.isabelleLemmas("deriveAll",deriveAllLLemmaist,proof=deriveAllLLemmaProof)
    symProtAllLemmas=isabelle.isabelleLemmas("symProtAll",symProtAllLemmaList,proof=symProtAllLemmaProof)
    res.append(deriveAllLLemmas)
    #res.append(symProtAllLemmas)
    return res

def genRuleSymLemma(rule):
    args = []
    
    if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
        args.append("N")
    oldArgs=args.copy()
    args=list(map(lambda a: isabelle.Const(a),args))
    ruleInst=isabelle.Fun(isabelle.Const(rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else
    predic1=isabelle.Fun(isabelle.Const("symProtRules'"),[isabelle.Const("N"),isabelle.Set(ruleInst)])  
    lemma1= isabelle.isabelleLemma(assms=[], conclusion=predic1,inLemmas=True)  
    env=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
    predic2=isabelle.Fun(isabelle.Const("wellFormedRule"),[env,isabelle.Const("N"),ruleInst])
    intros=["equivStatementParallel","equivStatementIteStm","equivStatementPermute"]
    proof=[isabelle.autoProof(unfolds=[rule.name])] if "N" not in oldArgs else \
        [isabelle.autoProof(unfolds=[rule.name],introITag="intro!",intros=intros), \
        isabelle.IsabelleApplyRuleProof(name="equivStatementSym"), isabelle.IsabelleApplyRuleProof(name="equivStatementPermute"), \
        isabelle.autoProof(simpadds=["mutualDiffVars_def"])]
    lemma2= isabelle.isabelleLemma(assms=[], conclusion=predic2,inLemmas=True)
    lemmas= isabelle.isabelleLemmas(name="sym"+rule.name,lemmas=[lemma1,lemma2],proof=proof)
    return lemmas


def genRuleDSymLemma(rule):
    args = []
    
    if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
        args.append("N")
    oldArgs=args.copy()
    args=list(map(lambda a: isabelle.Const(a),args))
    ruleInst=isabelle.Fun(isabelle.Const(rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else
    predic1=isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"),isabelle.Set(ruleInst)])  
    lemma1= isabelle.isabelleLemma(assms=[], conclusion=predic1,inLemmas=True)  
    env=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
    predic2=isabelle.Fun(isabelle.Const("wellFormedRule"),[env,isabelle.Const("N"),ruleInst])
    intros=["equivStatementParallel","equivStatementIteStm","equivStatementPermute"]
    proof=[isabelle.IsabelleApplyRuleProof(name=" DsymapplyRuleNone1"), \
           isabelle.autoProof(unfolds=["DsymapplyRuleNothing"]+[rule.name])]
    lemma2= isabelle.isabelleLemma(assms=[], conclusion=predic2,inLemmas=True)
    lemmas= isabelle.isabelleLemmas(name="Dsym"+rule.name,lemmas=[lemma1 ],proof=proof)
    return lemmas
    '''intros=["symParamRuleI2","symParamRuleI","symParamFormAnd","symParamFormForall", \
     "symParamFormForallExcl", "symParamFormImply" ,"symParamStatementParallel","symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte"] if paraNums==1 else \
         ["symParamRuleI2", "symParamRuleI", "symParamForm2And", "symParamForm2Forall1", "symParamForm2Forall2", "symParamFormForallExcl2", "symParamForm2Imply", \
              "symParamStatementParallel", "symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte" ]      
 
    proof1=isabelle.autoProof(unfolds=[ruleset.rule.name],introITag="intro!",intros=intros)
    vars = []
    hasForall=False
    if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
        vars.append("N")
        hasForall=True
    for var_decl in ruleset.var_decls:
        vars.append(var_decl.name)
    paraNums=len(vars) - 1 if hasForall else len(vars)
    args=list(map(lambda a: isabelle.Const(a),vars))
    ruleConst=isabelle.Fun(isabelle.Const(ruleset.rule.name),[isabelle.Const("N")]) if hasForall else isabelle.Const(ruleset.rule.name)
    ruleInst=isabelle.Fun(isabelle.Const(ruleset.rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
    predic1=isabelle.Fun(isabelle.Const("symParamRule"),[isabelle.Const("N"),ruleConst]) if paraNums==1 else isabelle.Fun(isabelle.Const("symParamRule2'"),[isabelle.Const("N"),ruleConst])
    lemma1= isabelle.isabelleLemma(assms=[], conclusion=predic1,inLemmas=True)
    env=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
    predic2=isabelle.Fun(isabelle.Const("wellFormedRule"),[env,isabelle.Const("N"),ruleInst])
    assms=[isabelle.Op("<=",isabelle.Const(n.name),isabelle.Const("N")) for n in  ruleset.var_decls]
    lemma2= isabelle.isabelleLemma(assms=assms, conclusion=predic2,inLemmas=True)
    intros=["symParamRuleI2","symParamRuleI","symParamFormAnd","symParamFormForall", \
     "symParamFormForallExcl", "symParamFormImply" ,"symParamStatementParallel","symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte"] if paraNums==1 else \
         ["symParamRuleI2", "symParamRuleI", "symParamForm2And", "symParamForm2Forall1", "symParamForm2Forall2", "symParamFormForallExcl2", "symParamForm2Imply", \
              "symParamStatementParallel", "symParamStatementForall", "symParamStatementForallExcl", "symParamStatementIte" ]      
 
    proof1=isabelle.autoProof(unfolds=[ruleset.rule.name],introITag="intro!",intros=intros)
    proof2=isabelle.autoProof(unfolds=["symParamForm_def  symParamStatement_def \
    symParamForm2_def symParamStatement2_def mutualDiffVars_def equivForm"])
    lemmas= isabelle.isabelleLemmas(name="sym"+ruleset.rule.name,lemmas=[lemma1,lemma2],proof=[proof1,proof2])
    return lemmas '''




  
def genInvariantSymLemma(inv):
    args = []
    if hasParamExpr(inv.inv):
        args.append("N")
    # Extract two parameters
    inv_t = inv.inv
    for _ in range(2):
        assert isinstance(inv_t, murphi.ForallExpr)
        args.append(inv_t.var)
        #inv_t = inv_t.expr
    args=list(map(lambda a: isabelle.Const(a),args))
    invN=isabelle.Fun(isabelle.Const(inv.name),[isabelle.Const("N")])
    invInst=isabelle.Fun(isabelle.Const(inv.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
    predic=isabelle.Fun(isabelle.Const("symParamForm2"),[isabelle.Const("N"),invN])
    proof=[isabelle.autoProof(unfolds=[inv.name]), \
        isabelle.introProof(intros=["symParamForm2Imply","symParamFormForallExcl1","symParamFormForallExcl2"]), \
        isabelle.autoProof(unfolds=["symParamForm2"])]
    lemma= isabelle.isabelleLemma(assms=[], conclusion=predic, \
            name="sym"+inv.name,proof=proof)
    return lemma   

'''
lemma symInvs:
  "symParamForm2 N (Lemma_1 N)"
  "symParamForm2 N (Lemma_2a N)"
  "symParamForm2 N (Lemma_2b N)"
  "symParamForm2 N (Lemma_3a N)"
  "symParamForm2 N (Lemma_3b N)"
  "symParamForm2 N (Lemma_4 N)"
  unfolding Lemma_1_def Lemma_2a_def Lemma_2b_def Lemma_3a_def Lemma_3b_def Lemma_4_def apply auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
    unfolding symParamForm2_def by auto
  done'''    

def genSymLemmas(prot):
    res=[]
    for decl in prot.decls:
        if isinstance(decl, murphi.MurphiRule):
            if (decl in prot.ori_rule_map.values()):
                pass #'''res.append(genRuleSymLemma(decl))'''
        #elif isinstance(decl, murphi.MurphiRuleSet):
        #    res.append(genRuleSetSymLemma(decl))
        elif isinstance(decl, murphi.MurphiInvariant):
            res.append(genInvariantSymLemma(decl))
    return res  

class extMurphiInvariant:
    def __init__(self, decl):
        assert(isinstance(decl,murphi.MurphiInvariant))
        self.decl = decl

    def __str__(self):
        return str(self.decl)

    def __repr__(self):
        return "murphiInvariant(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other,extMurphiInvariant) and self.decl == other.decl

    def genLemma1(self):
        typ = isabelle.formula
        args = []
        if hasParamExpr(self.decl.inv):
            typ = isabelle.FunType(isabelle.nat, typ)
            args.append("N")
        # Extract two parameters
        inv_t = self.decl.inv
        for _ in range(2):
            assert isinstance(inv_t, murphi.ForallExpr)
            typ = isabelle.FunType(isabelle.nat, typ)
            args.append(inv_t.var)
            inv_t = inv_t.expr
        #inv_t  = e1 ->e2 for some e1,e2 e2=forall i~=j-->  
        # 
        assert(isinstance(inv_t , murphi.OpExpr)&(inv_t.op=="->"))
        # print(args)
        excl_form = abstract.check_forall_exclude_form(inv_t.expr2)
        if excl_form:
            excl_var, concl = excl_form
            # print(excl_var)
            indsOccurInExpr1=exprHasIndex(inv_t.expr1,args)
            j=0
            for i in range(len(args)):
                if args[i] not in indsOccurInExpr1:
                    j=i
            del(args[j])
            var2=inv_t.expr2.var_decl.name
            assert ((var2 not in args))
            args.append(var2)
            
            expr2=inv_t.expr2.expr
            # print(type(expr2.expr1))
            # print((expr2.expr1.op))
            exprNeg=expr2.expr1 #exprNeg is "(i=j)"
            tmpLeft=exprNeg.expr1
            exprNeg.expr1=exprNeg.expr2
            exprNeg.expr2=tmpLeft
            self.lemma1Eqlemma =False
            res = translateForm(murphi.OpExpr("->",murphi.OpExpr("&",expr2.expr1,inv_t.expr1),expr2.expr2),args)
        else:
            if isinstance(inv_t.expr2 , murphi.OpExpr) and (inv_t.expr2.op=="=") and (inv_t.expr2.expr2.typ.name=="DATA"):
                var1=inv_t.expr2.expr1
                var2=inv_t.expr2.expr2
                e1=murphi.OpExpr("=",var1,murphi.VarExpr("d",murphi.VarType("DATA")))
                e2=murphi.OpExpr("=",var2,murphi.VarExpr("d",murphi.VarType("DATA")))
                e=murphi.OpExpr("->",e1,e2)
                e=murphi.OpExpr("->",inv_t.expr1,e)
                args.append("d")
                args=[item for item in args if item!= "N" and item!= "m"]
                args=sorted(args, key=lambda x:x[0])
                res = translateForm(e, args)
                self.lemma1Eqlemma =False
                typ=typ.range
            #vars.append(e.var)
            else:
                res = translateForm(self.decl.inv.expr.expr, args)
                self.lemma1Eqlemma =True
        return isabelle.Definition(self.decl.name+"'", typ, res, args=args, is_equiv=True)

    '''lemma absTransfLemma1:
    "M < N ⟹ M = 1 ⟹ l ≤ 1 ⟹ absTransfForm (env N) M (Lemma_1' N 0 l) = Lemma_1' N 0 l"
    unfolding Lemma_1'_def by auto'''
    def genabsTransfLemma(self):
        cond1=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
        cond2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
        cond3=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("1"))
        right=isabelle.Fun(isabelle.Const(self.decl.name+"'"),[isabelle.Const("N"),isabelle.Const("0"),isabelle.Const("l")])
        left=isabelle.Fun(isabelle.Const("absTransfForm"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),isabelle.Const("M"),
            right])
        proof=isabelle.autoProof(unfolds=[self.decl.name+"'"])
        return(isabelle.isabelleLemma(name="absTransf"+self.decl.name+"'",assms=[cond1,cond2,cond3],conclusion=isabelle.Op("=",left,right),proof=[proof]))
    '''"lemma absTransfLemma1M < N ⟹ M = 1 ⟹ l ≤ 1 ⟹ 
    safeForm  env  M (pf 0 i) ∧ deriveForm env (pf 0 i)
    unfolding Lemma_1'_def by auto"'''

    def genSafeAndderiveForm(self):
        cond1=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
        cond2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
        cond3=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("M"))
        cond4=isabelle.Op("<=",isabelle.Const("k"),isabelle.Const("M"))
        pred1=isabelle.Fun(isabelle.Const("safeForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("M"), \
            isabelle.Fun(isabelle.Const(self.decl.name+"'"),[isabelle.Const("N"),isabelle.Const("k"),isabelle.Const("l")])])
        pred2=isabelle.Fun(isabelle.Const("deriveForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),   \
            isabelle.Fun(isabelle.Const(self.decl.name+"'"),[isabelle.Const("N"),isabelle.Const("k"),isabelle.Const("l")])])
        return(isabelle.isabelleLemma(assms=[cond1,cond2,cond3,cond4], \
            conclusion=isabelle.Op("&",pred1,pred2),name="SafeAndderiveForm"+self.decl.name+"'", \
            proof=[isabelle.autoProof(unfolds=[self.decl.name+"'"])]))
    
    def genDsafeAndderiveForm(self):
        
        cond3=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("N"))
        cond4=isabelle.Op("<=",isabelle.Const("k"),isabelle.Const("N"))
        pred1=isabelle.Fun(isabelle.Const("DsafeForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), \
            isabelle.Fun(isabelle.Const(self.decl.name+"'"),[isabelle.Const("N"),isabelle.Const("k"),isabelle.Const("l")])])
        pred2=isabelle.Fun(isabelle.Const("deriveForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),   \
            isabelle.Fun(isabelle.Const(self.decl.name+"'"),[isabelle.Const("N"),isabelle.Const("k"),isabelle.Const("l")])])
        return(isabelle.isabelleLemma(assms=[cond3,cond4], \
            conclusion=isabelle.Op("&",pred1,pred2),name="DsafeAndderiveForm"+self.decl.name+"'", \
            proof=[isabelle.autoProof(unfolds=[self.decl.name+"'"])]))
  
    '''lemma strengthenVsObs1 [intro]:
    "strengthenVsObs (Lemma_1 N) (Lemma_1' N) N"
    unfolding Lemma_1_def Lemma_1'_def
    apply (rule strengthenVsObsDiff)
    unfolding symParamForm_def by auto'''
    def genstrengthenVsObsLemma(self):
        opd1=isabelle.Fun(isabelle.Const(self.decl.name),[isabelle.Const("N")])
        opd2=isabelle.Fun(isabelle.Const(self.decl.name+"'"),[isabelle.Const("N")])
        pred=isabelle.Fun(isabelle.Const("strengthenVsObs"),[opd1,opd2,isabelle.Const("N")])
        proof0=isabelle.autoProof(unfolds=[self.decl.name,self.decl.name+"'"],introITag="intro!",intros=["strengthenVsObsDiff","strengthenVsObsDiff1"])
         
        proof=proof0 if (not (self.lemma1Eqlemma)) \
            else isabelle.IsabelleApplyRuleProof(name="strengthenVsObsSame",unfolds=[self.decl.name,self.decl.name+"'"])
        proof1=isabelle.autoProof(unfolds=["symParamForm"])
        proofs=[proof,proof1] if (not (self.lemma1Eqlemma)) else [proof]
        return(isabelle.isabelleLemma(name="strengthenVsObs"+self.decl.name,assms=[],conclusion=pred, \
        proof=proofs))  #,attribs=["intro"],
              
    def genSymInvsItem(self):
        #symParamForm2 N name
        name=self.decl.name
        pred=isabelle.Fun(isabelle.Const("symParamForm2"),[isabelle.Const("N"),isabelle.Fun(isabelle.Const(name),[isabelle.Const("N")])])
        lemma=isabelle.isabelleLemma(assms=[],conclusion=pred,inLemmas=True)
        '''unfolding Lemma_1_def Lemma_2a_def Lemma_2b_def Lemma_3a_def Lemma_3b_def Lemma_4_def apply auto
                subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
                 unfolding symParamForm2_def by auto
        '''
        proof=isabelle.subgoalProof(proofs= \
            [isabelle.introProof(intros=["symParamForm2Imply", "symParamFormForallExcl1", "symParamFormForallExcl2"]), \
             isabelle.autoProof(unfolds=["symParamForm2"])   ])

        return (name,lemma,proof)

    def genSymInvsItem1(self):
        #symParamForm2 N name
        name=self.decl.name+"'"
        pred=isabelle.Fun(isabelle.Const("symParamForm2"),[isabelle.Const("N"),isabelle.Fun(isabelle.Const(name),[isabelle.Const("N")])])
        lemma=isabelle.isabelleLemma(assms=[],conclusion=pred,inLemmas=True)
        '''unfolding Lemma_1_def Lemma_2a_def Lemma_2b_def Lemma_3a_def Lemma_3b_def Lemma_4_def apply auto
                subgoal apply (intro symParamForm2Imply symParamFormForallExcl2)
                 unfolding symParamForm2_def by auto
        '''
        proof=isabelle.subgoalProof(proofs= \
            [isabelle.introProof(intros=["symParamForm2Imply", "symParamFormForallExcl1","symParamFormForallExcl2"]), \
             isabelle.autoProof(unfolds=["symParamForm2"])   ])

        return (name,lemma,proof)

    def test(self):
        ...
        #print(self.decl.var)  
        #print(type(self.decl.var))
        # print(self.decl.inv.expr.var_decl) 
        # print(type(self.decl.inv.expr))


class extMurphiRule:
    def __init__(self, decl):
        assert(isinstance(decl,murphi.MurphiRule))
        self.decl = decl

    def __str__(self):
        return str(self.decl)

    def __repr__(self):
        return "murphiRule(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, extMurphiRule) and self.decl == other.decl

    '''lemma strengthenVsObsLs_lemmasFor_NI_InvAck1:
    "strengthenVsObsLs (lemmasFor_NI_InvAck1 N) (lemmasFor_NI_InvAck1' N) N"
     by (auto simp add: strengthenVsObsLs_def lemmasFor_NI_InvAck1_def lemmasFor_NI_InvAck1'_def)'''

    def genLemmastrengthenVsObsLs(self):
        name="strengthenVsObsLs_lemmasFor_"+self.decl.name
        opd1=isabelle.Fun(isabelle.Const("lemmasFor_"+self.decl.name),[isabelle.Const("N")])
        opd2=isabelle.Fun(isabelle.Const("lemmasFor_"+self.decl.name+"'"),[isabelle.Const("N")])
        pred=isabelle.Fun(isabelle.Const("strengthenVsObsLs"),[opd1,opd2,isabelle.Const("N")])
        unfolds=["strengthenVsObsLs", "lemmasFor_"+self.decl.name, "lemmasFor_"+self.decl.name+"'"]
        proof=isabelle.autoProof(unfolds=unfolds)
        lemma=isabelle.isabelleLemma(name=name,assms=[],conclusion=pred,proof=[proof])
        return(lemma)

    def genStrengthenLemmasDef1(self,item):
        name="lemmasFor_"+self.decl.name+"'"
        val=isabelle.List(*tuple(isabelle.Fun(isabelle.Const(lemma+"'"), [isabelle.Const("N")]) for lemma in item["strengthen"]))
        typ = isabelle.FunType(isabelle.nat, isabelle.ListType(isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.formula))))
        defLemma=isabelle.Definition(name=name, typ=typ, val=val,args=["N"])
        return(defLemma)

    def genFitenvLemma(self):
        name="lemma"+self.decl.name+"_fitEnv"
        hasNList=[isabelle.Const("N")]  if (hasParamExpr(self.decl.cond) or any(hasParamCmd(c) for c in self.decl.cmds)) else []
        assm1=isabelle.Fun(isabelle.Const("formEval"), [isabelle.Fun(isabelle.Const("pre"),[isabelle.Const("r")]),isabelle.Const("s") ])  
        assm2=isabelle.Fun(isabelle.Const("fitEnv"), [isabelle.Const("s"),isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) ])  
        assm3=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const(self.decl.name+"_refs"),hasNList) )
        conclusion=isabelle.Fun(isabelle.Const("fitEnv"), \
        [isabelle.Fun(isabelle.Const("trans1"),[isabelle.Fun(isabelle.Const("act"),[isabelle.Const("r")]),isabelle.Const("s")]), \
        isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) \
        ]) 
        atrributs=["intro"]
        unfolds=[ self.decl.name+"_refs", self.decl.name+"_ref"]
        proof=isabelle.autoProof(unfolds=unfolds)
         
        return(isabelle.isabelleLemma(name=name,assms=[assm1,assm2,assm3],conclusion=conclusion,proof=[proof]))


    def genSafeAndDeriveLemma(self,nameOfLemmas1):
        name="SafeAndDerive"+self.decl.name
        '''hasNList=[isabelle.Const("N")]  if (hasParamExpr(self.decl.cond) or any(hasParamCmd(c) for c in self.decl.cmds)) else []
        assm1=isabelle.Fun(isabelle.Const("formEval"), [isabelle.Fun(isabelle.Const("pre"),[isabelle.Const("r")]),isabelle.Const("s") ])  
        assm2=isabelle.Fun(isabelle.Const("fitEnv"), [isabelle.Const("s"),isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) ])  
        assm3=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const(self.decl.name+"_refs"),hasNList) )
        conclusion=isabelle.Fun(isabelle.Const("fitEnv"), \
        [isabelle.Fun(isabelle.Const("trans1"),[isabelle.Fun(isabelle.Const("act"),[isabelle.Const("r")]),isabelle.Const("s")]), \
        isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) \
        ]) 
        atrributs=["intro"]
        unfolds=[ self.decl.name+"_refs", self.decl.name+"_ref"]
        proof=isabelle.autoProof(unfolds=unfolds)'''

        cond1=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
        cond2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
        cond3=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("M"))
        cond31=isabelle.Op("<=",isabelle.Const("k"),isabelle.Const("M"))
        cond4=isabelle.Op(":",isabelle.Const("pf"),isabelle.Fun(isabelle.Const("set"),[(isabelle.Fun(isabelle.Const("lemmasFor_"+self.decl.name+"'"),[isabelle.Const("N")]))]))
        cond5=isabelle.Op(":",isabelle.Const("pf"),isabelle.Fun(isabelle.Const("set"),[isabelle.Const("pinvL")]))
        pred1=isabelle.Fun(isabelle.Const("safeForm"), \
                [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("M"), \
                isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
        pred2=isabelle.Fun(isabelle.Const("deriveForm"), \
                [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),   \
                isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
        unfolds=["lemmasFor_"+self.decl.name+"'"]
        usings=["SafeAndderiveForm"+n for n in nameOfLemmas1]
        lemma=(isabelle.isabelleLemma(assms=[cond1,cond2,cond3,cond31,cond4 ], \

            conclusion=isabelle.Op("&",pred1,pred2),name=name, \
            proof=[isabelle.autoProof(unfolds=unfolds,usings=usings)]))
         
        return(lemma)


'''generate items on strengthening and abstraction, firstly generate strengthened rule and abstract resultings

lemma Idle_strengthen:
  "strengthenRuleByFrmL2 (map2' (lemmasFor_Idle N) j i) (Idle i) = Idle_ref N i"
  unfolding lemmasFor_Idle_def Lemma_1_def Idle_def Idle_ref_def by auto


lemma IdleStrengthRel:"strengthenRel (Idles N)  (set (InvS N)) (Idle_refs N) N "
  apply(unfold Idles_def Idle_refs_def)
  apply(rule_tac ?lemmasFor_r="lemmasFor_Idle" in strengthenExt1)
  using Idle_strengthen apply presburger
  apply(unfold InvS_def,auto)    
  done


definition lemmasFor_Idle :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list" where
  "lemmasFor_Idle N \<equiv> [Lemma_1 N]"

definition lemmasFor_Idle' :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list" where
  "lemmasFor_Idle' N \<equiv> [Lemma_1' N]"

definition InvS :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list list" where
  "InvS N \<equiv> [lemmasFor_Idle N]"
'''


class extMurphiRuleSet:
    def __init__(self, decl, strengthen=None):
        assert(isinstance(decl,murphi.MurphiRuleSet))
        self.decl = decl
        self.strengthen=strengthen

    def __str__(self):
        return str(self.decl)

    def __repr__(self):
        return "murphiRuleset(%s)" % (', '.join(repr(typ) for typ in self.typs))

    def __eq__(self, other):
        return isinstance(other, extMurphiRuleSet) and self.decl == other.decl

    '''lemma strengthenVsObsLs_lemmasFor_NI_InvAck1:
    "strengthenVsObsLs (lemmasFor_NI_InvAck1 N) (lemmasFor_NI_InvAck1' N) N"
     by (auto simp add: strengthenVsObsLs_def lemmasFor_NI_InvAck1_def lemmasFor_NI_InvAck1'_def)'''

    def genLemmastrengthenVsObsLs(self):
        name="strengthenVsObsLs_lemmasFor_"+self.decl.rule.name
        opd1=isabelle.Fun(isabelle.Const("lemmasFor_"+self.decl.rule.name),[isabelle.Const("N")])
        opd2=isabelle.Fun(isabelle.Const("lemmasFor_"+self.decl.rule.name+"'"),[isabelle.Const("N")])
        pred=isabelle.Fun(isabelle.Const("strengthenVsObsLs"),[opd1,opd2,isabelle.Const("N")])
        unfolds=["strengthenVsObsLs", "lemmasFor_"+self.decl.rule.name, "lemmasFor_"+self.decl.rule.name+"'"]
        autoIntros=["strengthenVsObs"+k for k in self.strengthen]
        if self.strengthen==[]:
            proof=isabelle.autoProof(unfolds=unfolds)
        else:
            proof=isabelle.autoProof(unfolds=unfolds,introITag="intro",intros=autoIntros)
        lemma=isabelle.isabelleLemma(name=name,assms=[],conclusion=pred,proof=[proof])
        return(lemma)

    def genStrengthenLemmasDef1(self,item):
        name="lemmasFor_"+self.decl.rule.name+"'"
        val=isabelle.List(*tuple(isabelle.Fun(isabelle.Const(lemma+"'"), [isabelle.Const("N")]) for lemma in item["strengthen"]))
        typ = isabelle.FunType(isabelle.nat, isabelle.ListType(isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.formula))))
        defLemma=isabelle.Definition(name=name, typ=typ, val=val,args=["N"])
        return(defLemma)

    def genFitenvLemma(self):
        name="lemma"+self.decl.rule.name+"_fitEnv"
        vars=list(map(lambda x:x.name,self.decl.var_decls))
        hasNList=[isabelle.Const("N")] if len(self.decl.var_decls)!=0  and not("d" in vars) else \
        [isabelle.Const("D"),isabelle.Const("N")] if len(self.decl.var_decls)!=0   else \
            ([isabelle.Const("N")] if (hasParamExpr(self.decl.rule.cond) or any(hasParamCmd(c) for c in self.decl.rule.cmds)) else [])
        assm1=isabelle.Fun(isabelle.Const("formEval"), [isabelle.Fun(isabelle.Const("pre"),[isabelle.Const("r")]),isabelle.Const("s") ])  
        assm2=isabelle.Fun(isabelle.Const("fitEnv"), [isabelle.Const("s"),isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) ])  
        assm3=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const(self.decl.rule.name+"_refs"),hasNList) )
        conclusion=isabelle.Fun(isabelle.Const("fitEnv"), \
        [isabelle.Fun(isabelle.Const("trans1"),[isabelle.Fun(isabelle.Const("act"),[isabelle.Const("r")]),isabelle.Const("s")]), \
        isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) \
        ]) 
        #atrributs=["intro"]
        unfolds=[ self.decl.rule.name+"_refs", self.decl.rule.name+"_ref"]
        proof=isabelle.autoProof(unfolds=unfolds)
        #attribs=atrributs, 
        return(isabelle.isabelleLemma(name=name,assms=[assm1,assm2,assm3],conclusion=conclusion,proof=[proof]))

    def genSafeAndDeriveLemma(self,nameOfLemmas1):
        name="SafeAndDerive"+self.decl.rule.name
        '''hasNList=[isabelle.Const("N")]  if (hasParamExpr(self.decl.cond) or any(hasParamCmd(c) for c in self.decl.cmds)) else []
        assm1=isabelle.Fun(isabelle.Const("formEval"), [isabelle.Fun(isabelle.Const("pre"),[isabelle.Const("r")]),isabelle.Const("s") ])  
        assm2=isabelle.Fun(isabelle.Const("fitEnv"), [isabelle.Const("s"),isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) ])  
        assm3=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const(self.decl.name+"_refs"),hasNList) )
        conclusion=isabelle.Fun(isabelle.Const("fitEnv"), \
        [isabelle.Fun(isabelle.Const("trans1"),[isabelle.Fun(isabelle.Const("act"),[isabelle.Const("r")]),isabelle.Const("s")]), \
        isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]) \
        ]) 
        atrributs=["intro"]
        unfolds=[ self.decl.name+"_refs", self.decl.name+"_ref"]
        proof=isabelle.autoProof(unfolds=unfolds)'''

        cond1=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
        cond2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
        cond3=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("M"))
        cond31=isabelle.Op("<=",isabelle.Const("k"),isabelle.Const("M"))
        cond4=isabelle.Op(":",isabelle.Const("pf"),isabelle.Fun(isabelle.Const("set"),[(isabelle.Fun(isabelle.Const("lemmasFor_"+self.decl.rule.name+"'"),[isabelle.Const("N")]))]))
        #cond5=isabelle.Op(":",isabelle.Const("pf"),isabelle.Fun(isabelle.Const("set"),[isabelle.Const("pinvL")]))
        pred1=isabelle.Fun(isabelle.Const("safeForm"), \
                [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("M"), \
                isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
        pred2=isabelle.Fun(isabelle.Const("deriveForm"), \
                [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),   \
                isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
        unfolds=["lemmasFor_"+self.decl.rule.name+"'"]
        usings=["SafeAndderiveForm"+n for n in nameOfLemmas1]
        lemma=(isabelle.isabelleLemma(assms=[cond1,cond2,cond3,cond31,cond4], \

            conclusion=isabelle.Op("&",pred1,pred2),name=name, \
            proof=[isabelle.autoProof(unfolds=unfolds,usings=usings)]))
         
        return(lemma)

def swapListEle(a,i,j):
    
    tmpStr=""
    for k in range(len(a)):
        tmpStr=tmpStr+ a[i].__str__()+"|"
    print(tmpStr+str(i)+str(j)+str(len(a)))
    '''assert(i<len(a) and j<len(a))'''
    temp=a[i]
    a[i]=a[j]
    a[j]=temp

def chooseNodeDecls(decls):
    for decl in decls:
        print(decl.typ.name)
    return(list(filter(lambda x: x.typ.name == "NODE", decls)))


def genSterengthenLemmas(prot,strengthenSpec):
    #nonlocal absRuleDefList
    def getRuleOrRuleset(item):
        try: 
            return(item["ruleset"])
        except (KeyError):
            return(item["rule"])

    def getAllProtRuleNames():
        list=[]
        for k in prot.ori_rule_map.keys():
            if isinstance(prot.ori_rule_map[k],murphi.MurphiRule):
                list.append(k)
        return(list)

    def getAllProtRuleSetNames():
        list=[]
        for k in prot.ori_rule_map.keys():
            if isinstance(prot.ori_rule_map[k],murphi.MurphiRuleSet):
                list.append(k)
        return(list)

    def toProof(x):
        print("x.export()="+x.export())
        if isinstance(x,isabelle.Set):#x==isabelle.Set(isabelle.Const("skipRule")):
            proof=[isabelle.autoProof(goalNum=1)]
        else:
            name=x.fun.name
            name0=name[:-1]
            args=list(map(lambda x: x.name,x.args))
            if not("D" in args):
                if not(name.startswith("ABS")):
                    proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DsymapplyRuleNone1")
                    proof2=isabelle.autoProof(usings=["Dsym"+name0],goalNum=1)
                    proof=[proof1,proof2]
                else:
                    #proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DsymapplyRuleNone1")
                    proof=[isabelle.autoProof(usings=[name+"_def","Dsym"+name0],goalNum=1)]
            else:
                if not(name.startswith("ABS")):
                    proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DIsymParaRuleInfSymRuleSetD1")
                    proof2=isabelle.autoProof(usings=["Dsym"+name0],goalNum=1)   
                    proof=[proof1,proof2] 
                else:
                    proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DsymParaRuleInfSymRuleSet")
                    proof2=isabelle.autoProof(usings=["Dsym"+name0],goalNum=1)  
                    proof=[proof1,proof2] 
        return(proof)
    '''lemma Dabs_Store_str : 
  "⟦ i ≤ N ∧ d=0 ⟧ ⟹DabsTransfRule (env N)   (Store_str d i) = Store_str d i"
  "⟦   d=0 ⟧ ⟹ DabsTransfRule (env N)   (ABS_Store d ) = ABS_Store d"
  
  "⟦ i ≤ N ∧ 0<d ⟧ ⟹DabsTransfRule (env N)   (Store_str d i) = Store_str 1 i"
  "⟦  0< d ⟧ ⟹ DabsTransfRule (env N)   (ABS_Store d ) = ABS_Store 1"
  unfolding Store_str_def Store_str_def ABS_Store_def
  apply (auto simp add: Let_def)
  done'''
    def toDabsRuleLemma(x):
        def DabsTransfRuleTerm(ts):
            return(isabelle.Fun(isabelle.Const("DabsTransfRule"),ts))
        
        print("x.export()="+x.export())
        for k in x.args:
            print("x.rep()="+k.__repr__())
        arg1=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
        left=DabsTransfRuleTerm([arg1])
        left=isabelle.Op("`", left, x)

        if isinstance(x,isabelle.Set):#x==isabelle.Set(isabelle.Const("skipRule")):
            arg2=isabelle.Const("skipRule")
            
            conclusion=isabelle.eq(left,x)
            proof=[isabelle.autoProof(unfolds=["skipRule"])]
            lemma=isabelle.isabelleLemma(name="DAbs_skipRuleSet",assms=[],conclusion=conclusion,proof=proof)
        else:
            name=x.fun.name
            lemmaN="DAbs_"+name
            name0=name[:-1]
            args=list(map(lambda x: x.name,x.args))
            argsAtRight=list(map(lambda x: isabelle.Const("N") if x=="N" else \
                                 isabelle.Const("1")   , args))
            argsOnD=filter(lambda x: x=="D",args)
            assums=list(map(lambda x: isabelle.Op("<",isabelle.Const("0"),isabelle.Const(x) ) ,argsOnD)) 
            #assums=filter(lambda x:x!=None,assums)
            #left=isabelle.Op("`", \
            #isabelle.Fun(isabelle.Const("DabsTransfRule"),[]),x)   
            if not("D" in args):
                right=isabelle.Fun(isabelle.Const(name), argsAtRight)
                conclusion=isabelle.eq(left,right)
                if not(name.startswith("ABS")):
                        
                    proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DabsGenInv")
                    proof2=isabelle.autoProof(unfolds=[name0])
                    proof=[proof1,proof2]
                    lemma=isabelle.isabelleLemma(name=lemmaN,assms=[],conclusion=conclusion,proof=proof)
                else:
                     
                    proof2=isabelle.autoProof(unfolds=[name,name0])
                    proof=[proof2]
                    lemma=isabelle.isabelleLemma(name=lemmaN,assms=[],conclusion=conclusion,proof=proof)

            else:
                right=isabelle.Fun(isabelle.Const(name), argsAtRight)
                conclusion=isabelle.eq(left,right)   
                if not(name.startswith("ABS")):
                        
                    proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DabsGenDd")
                    proof2=isabelle.autoProof(unfolds=[name0])
                    proof=[proof1,proof2]
                    lemma=isabelle.isabelleLemma(name=lemmaN,assms=assums,conclusion=conclusion,proof=proof)
                else:
                    proof1=isabelle.IsabelleApplyRuleProof(unfolds=[name],name= "DabsGen") 
                    proof2=isabelle.autoProof(unfolds=[name,name0])
                    proof=[proof1,proof2]
                    lemma=isabelle.isabelleLemma(name=lemmaN,assms=assums,conclusion=conclusion,proof=proof) 
                
        return(lemma)
    
    '''lemma lemmaIdle_keepData : 
  "[|formEval (pre r) s;(∃d. s (Para ''n.data'' i) = data d ∧ d ≤ D);r : IdleRep_strs  N|] ==> 
  (∃d. (trans1 (act r) s) (Para ''n.data'' i) = data d ∧ d ≤ D) "
  unfolding IdleRep_strs_def IdleRep_str_def
  apply auto
  done'''
    
    def toKeepDataLemma(x):
        if isinstance(x,isabelle.Set):#x==isabelle.Set(isabelle.Const("skipRule")):
            name="skipRule"
            lemmaN="lemma"+"skipRule"+"keepData"
            proof=isabelle.autoProof()
        else:
            name=x.fun.name
            lemmaN="lemma"+name+"keepData"
            name0=name[:-1]
            proof=isabelle.autoProof(unfolds=[name,name0])
        assm1=isabelle.Fun(isabelle.Const("formEval"),[isabelle.Fun(isabelle.Const("pre"),[isabelle.Const("r")]),\
                                                                   isabelle.Const("s") ])
        '''assm2=isabelle.Quant("ex","d",isabelle.Op("&",\
                                                  isabelle.Op("=",isabelle.Fun(isabelle.Const("s"),[isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("''n.data''"),isabelle.Const("i")])]),isabelle.Fun(isabelle.Const("data"),[isabelle.Const("d")])),\
                                                  isabelle.Op("<=", isabelle.Const("d"),isabelle.Const("D") )))'''
        assm21=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),isabelle.Const("s"),isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("''n.data''"),isabelle.Const("i")])])
        assm22=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),isabelle.Const("s"),isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("''memDATA''")])])
        assm23=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),isabelle.Const("s"),isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("''auxDATA''")])])
       
        assm2=isabelle.Op("&",isabelle.Op("&",assm21,assm22),assm23)
        assm3=isabelle.Op(":",isabelle.Const("r"),x)
        #assm2=isabelle.Quant("ex","d",assm2)
        #nt=isabelle.Fun(isabelle.Fun(isabelle.Const("trans1"),[isabelle.Fun(isabelle.Const("act"),[isabelle.Const("r")]),isabelle.Const("s")]),[isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("''n.data''"),isabelle.Const("i")])])
        nt=isabelle.Fun(isabelle.Const("trans1"),[isabelle.Fun(isabelle.Const("act"),[isabelle.Const("r")]),isabelle.Const("s")])
        con21=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),nt,isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("''n.data''"),isabelle.Const("i")])])
        con22=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),nt,isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("''memDATA''")])])
        con23=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),nt,isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("''auxDATA''")])])
       
        conclusion=isabelle.Op("&",isabelle.Op("&",con21,con22),con23)
        
        lemma=isabelle.isabelleLemma(name=lemmaN,assms=[assm1,assm2,assm3],conclusion=conclusion,proof=[proof]) 
        
        return(lemma)

    def genLemmaAllReachKeepData(absRules,initSpecs):
        
        name="ReachABSKeepData"
        assm1=isabelle.Fun(isabelle.Const("reachableUpTo"), [(isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("M")])), \
            isabelle.Fun(isabelle.Const("ABS_rules"), [isabelle.Const("D"),isabelle.Const("M")]), isabelle.Const("k"), isabelle.Const("s")] )
        assm2=isabelle.Op("<=",isabelle.Const("i"),isabelle.Const("M"))
        con21=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),isabelle.Const("s"),isabelle.Fun(isabelle.Const("Para"),[isabelle.Const("''n.data''"),isabelle.Const("i")])])
        con22=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),isabelle.Const("s"),isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("''memDATA''")])])
        con23=isabelle.Fun(isabelle.Const("varKeepData"),[isabelle.Const("D"),isabelle.Const("s"),isabelle.Fun(isabelle.Const("Ident"),[isabelle.Const("''auxDATA''")])])
        
        con2=isabelle.Op("&",isabelle.Op("&",con21,con22),con23)
        conclusion=isabelle.Quant("ex","d",con2)
        '''proof1=isabelle.IsabelleApplyRuleProof(name="invIntro", \
            rule_tac="?fs=\" (allInitSpecs N)\"  and rs=\"(rule_refs N)\" and k=\"k\"")'''
        proof1=isabelle.IsabelleApplyEruleProof(name="invIntro1")
        proof2=isabelle.autoProof(unfolds=["allInitSpecs"])
        proof2=isabelle.subgoalProof(fors=["s0"],proofs=[proof2])
        rules=list(map(lambda x: "skipRule" if isinstance(x,isabelle.Set) else x.fun.name,absRules))
        autoIntros=["Un_iff"]+["lemma"+k+"keepData" for k in rules]
        proof3=isabelle.subgoalProof(fors=["r","sk"],proofs=[isabelle.metisProof(unfolds=["ABS_rules"],intros=autoIntros)])
        '''proof7=isabelle.subgoalProof(fors=[],proofs=[isabelle.autoProof()])
        proof8s=[isabelle.autoProof(unfolds=["rule_refs"])] + \
            [isabelle.autoProof(unfolds=[n+"_refs",n+"_ref"]) for n in prot.ori_rule_map.keys()]
        proof8=isabelle.subgoalProof(fors=[],proofs=proof8s)
        proof9=isabelle.autoProof()'''
        lemma=isabelle.isabelleLemma(assms=[assm1,assm2],conclusion=con2,name=name,proof=[proof1,proof2,proof3])
        return(lemma)   
    '''lemma DwellFormedABS_rules : 
    "[|r : ABS_rules D M |] ==> DwellFormedRule (env N)  r"
     apply (auto simp add: ABS_rules_def   Try_strs_def Crit_strs_def Exit_strs_def 
    IdleRep_strs_def Store_strs_def ABS_Crits_def  ABS_IdleReps_def  ABS_Stores_def Store_str_def symTry_str symCrit_str symExit_str symIdle_str symStore_str)
    done'''
    def genDwellFormLemma(absRules):    
        name="DwellFormedABS_rules"
        assm=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const("ABS_rules"), [isabelle.Const("D"),isabelle.Const("M")]))
        con=isabelle.Fun(isabelle.Const("DwellFormedRule"), [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),isabelle.Const("r")])
        rules=list(map(lambda x: "skipRule_def" if isinstance(x,isabelle.Set) else x.fun.name+"_def"+" "+x.fun.name[:-1]+"_def",absRules))
        #autoIntros=["Un_iff"]+["lemma"+k+"keepData" for k in rules]
        proof=isabelle.autoProof(simpadds=rules)
        lemma=isabelle.isabelleLemma(assms=[assm],conclusion=con,name=name,proof=[proof])
        return(lemma)  

    res=[]
    InvSList=[]
    InvS1List=[]
    res1=[]
    deriveAllLLemmaist=[]
    symProtAllLemmaList=[]
    dsymProtAllLemmaList=[]
    refRulesDefList=[]
    defOfabsRules=[]
    
    absRuleDefList=[]
    absRuleDefList1=[]

    deriveAllLLemmaProofUnfolds1=[]
    symProtAllLemmaProofUsings2=[]
    dsymProtAllLemmaProofUsings2=[]
    absLemmasOnSets=[]

    for item in strengthenSpec:
        passName=""
        try:
            ruleset=prot.ori_rule_map[item["ruleset"]]
            vars = []
            hasForall=False
            if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds):
                vars.append("N")
                hasForall=True
            for var_decl in ruleset.var_decls:
                vars.append(var_decl.name)
            paraNums=len(vars) - 1 if hasForall else len(vars)
            args=list(map(lambda a: isabelle.Const(a),vars))
            ruleConst=isabelle.Const(ruleset.rule.name)
            #generate definition for strengthening lemmas for this rule
            typ = isabelle.FunType(isabelle.nat, isabelle.ListType(isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.formula))))
            #val=isabelle.List(tuple(map(lambda lemma:isabelle.Fun(isabelle.Const(lemma), [isabelle.Const("N")]),item["strengthen"])))
            # print(type(tuple(isabelle.Fun(isabelle.Const(lemma), [isabelle.Const("N")]) for lemma in item["strengthen"])))
            val=isabelle.List(*tuple(isabelle.Fun(isabelle.Const(lemma), [isabelle.Const("N")]) for lemma in item["strengthen"]))
            defLemma=isabelle.Definition(name="lemmasFor_"+ruleset.rule.name, \
            typ=typ, val=val,args=["N"])
            ruleInst=isabelle.Fun(isabelle.Const(ruleset.rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
            #generate r_ref

            #ruleSet1=ruleset
            r_ref=murphi.MurphiRule(name=ruleset.rule.name+"_ref",cond=ruleset.rule.cond,cmds=ruleset.rule.cmds)
            strengthenCopy=item["strengthen"].copy()
            strengthenCopy.reverse()
            for lemma in  strengthenCopy:
                lemmaC=prot.lemma_map[lemma].inv
                r_ref=abstract.strengthen_2(r_ref,lemmaC)
            oldRuleName=ruleset.rule.name
            #r_ref.name=ruleset.rule.name+"_ref"
            ruleSet1=murphi.MurphiRuleSet(var_decls=ruleset.var_decls,rule=r_ref)
            # print("test ruleset.rule.name=%s"%ruleset.rule.name)
            #generate lemmas on r_strengthen
            declVars=list(map(lambda x:x.name,ruleset.var_decls))
            oldhasNList=[isabelle.Const("N")] if hasParamExpr(ruleset.rule.cond) or any(hasParamCmd(c) for c in ruleset.rule.cmds) else []
        
            hasNList=[isabelle.Const("N")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
            
            left1=isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("j"),isabelle.Const("i")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList+[isabelle.Const("i")])])  if (paraNums==1) and (not("d" in declVars)) else\
                isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("i"),isabelle.Const("j")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList+[isabelle.Const("i"),isabelle.Const("j")])]) if (paraNums==2) and (not("d" in declVars)) else\
                isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("j"),isabelle.Const("i")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList+[isabelle.Const("d"),isabelle.Const("i")])]) if (paraNums==2) and (("d" in declVars)) else\
                isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("i"),isabelle.Const("j")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList+[isabelle.Const("d"),isabelle.Const("i"),isabelle.Const("j")])])  
                
            right1=isabelle.Fun(isabelle.Const(r_ref.name),hasNList+[isabelle.Const("i")]) if (paraNums==1)  and (not("d" in declVars)) else \
                isabelle.Fun(isabelle.Const(r_ref.name),hasNList+[isabelle.Const("i"),isabelle.Const("j")]) if (paraNums==2) and (not("d" in declVars)) else\
                isabelle.Fun(isabelle.Const(r_ref.name),hasNList+[isabelle.Const("d"),isabelle.Const("i")]) if (paraNums==2) and (("d" in declVars)) else\
                isabelle.Fun(isabelle.Const(r_ref.name),hasNList+[isabelle.Const("d"),isabelle.Const("i"),isabelle.Const("j")])
            eq1=isabelle.eq(left1,right1)
            lemmas_def=" ".join(lemma+"_def" for lemma in item["strengthen"])
            proof=isabelle.autoProof(unfolds=[("lemmasFor_%s_def %s %s_def %s_ref")%(oldRuleName,lemmas_def,oldRuleName,oldRuleName)])
            lemma1= isabelle.isabelleLemma(name=oldRuleName+"_strengthen",assms=[], conclusion=eq1,proof=[proof]) 
            #generate lemmas on r_StrengthRel
            pred2=isabelle.Fun(isabelle.Const("strengthenRel"), [ \
                isabelle.Fun(isabelle.Const(oldRuleName+"s"),[isabelle.Const("N")]), \
                isabelle.Fun(isabelle.Const("set"), [isabelle.Fun(isabelle.Const("InvS"),[isabelle.Const("N")])]), \
                isabelle.Fun(isabelle.Const(oldRuleName+"_refs"), [isabelle.Const("N")]),
                isabelle.Const("N")]) if not(("d" in declVars)) else \
                isabelle.Fun(isabelle.Const("strengthenRel"), [ \
                isabelle.Fun(isabelle.Const(oldRuleName+"s"),[isabelle.Const("D"),isabelle.Const("N")]), \
                isabelle.Fun(isabelle.Const("set"), [isabelle.Fun(isabelle.Const("InvS"),[isabelle.Const("N")])]), \
                isabelle.Fun(isabelle.Const(oldRuleName+"_refs"), [isabelle.Const("D"),isabelle.Const("N")]),
                isabelle.Const("N")])  
            proof21TacName="strengthenExt1" if len(ruleset.var_decls)==1 else \
                "strengthenExt2" if not(("d" in declVars)) else \
                "strengthenDExt1"  
            proof21=isabelle.IsabelleApplyRuleProof(name=proof21TacName,unfolds=["%ss_def %s_refs"%(oldRuleName,oldRuleName)],
            rule_tac="?lemmasFor_r=\"lemmasFor_"+oldRuleName+"\"")
            proof22=isabelle.presburgerProof(usings=[oldRuleName+"_strengthen"])
            proof23=isabelle.autoProof(unfolds=["InvS"])
            lemma2=isabelle.isabelleLemma(name=oldRuleName+"StrengthRel",assms=[], conclusion=pred2,proof=[proof21,proof22,proof23]) 
            predOfLemma=isabelle.Fun(isabelle.Const(("lemmasFor_%s"%oldRuleName)),[isabelle.Const("N")]) 
            predOfLemma1=isabelle.Fun(isabelle.Const(("lemmasFor_%s"%oldRuleName+"'")),[isabelle.Const("N")]) 
            #abstract r_ref
            absRule=[]
            absRules=[]
            suffix=""
            if isinstance(ruleSet1,murphi.MurphiRuleSet):
                limits=dict()
                if len(ruleSet1.var_decls)==1:
                    limits[ruleSet1.var_decls[0].name]=False
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    if absr!=ruleSet1.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
                        absRule.append(absr)

                elif len(ruleSet1.var_decls)==2:
                    limits[ruleSet1.var_decls[0].name]=False
                    limits[ruleSet1.var_decls[1].name]=True
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    absrulesetdecls=ruleSet1.var_decls[1:2]
                    if absr!=ruleSet1.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)
                        absRules.append(absr)

                    limits=dict()
                    limits[ruleSet1.var_decls[1].name]=False
                    limits[ruleSet1.var_decls[0].name]=True
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    absrulesetdecls=ruleSet1.var_decls[0:1]
                    if absr!=ruleSet1.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)
                        absRules.append(absr)
                    limits=dict()
                    limits[ruleSet1.var_decls[0].name]=False
                    limits[ruleSet1.var_decls[1].name]=False
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    if absr!=ruleSet1.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
                        absRule.append(absr)
            def11,lemma11,lemma21,dlemma21,term11,unfolds1,usings1=translateRuleSets(ruleSet1)
            deriveAllLLemmaist.append(lemma11)
            symProtAllLemmaList.append(lemma21)
            dsymProtAllLemmaList.append(dlemma21)
            refRulesDefList.append(term11)
            deriveAllLLemmaProofUnfolds1.extend(unfolds1)
            symProtAllLemmaProofUsings2.extend(usings1)

            InvSList.append(predOfLemma)
            InvS1List.append(predOfLemma1)
            res.append(defLemma)
            res.append(translateRuleSet(ruleSet1))
            res.append(genRuleSetSymLemma(ruleSet1))
            res.append(genRuleSetDSymLemma(ruleSet1))
            res.append(def11)
            res.append(lemma1)
            res1.append(lemma2)
            
            '''for absr in absRules:
                res.append(translateRuleSet(absr))
                defA,lemmaA1,lemmaA2,termA,unfoldsA,usingsA=translateRuleSets(absr)
                res.append(defA)'''
            '''generate1. lemmas on abstraction for r_refs by json:
            2. definitions for    ABS_rules,  ABS_rules' 
            "abstract":[{"cond":{"i": false},"answer":"ABS_Idle"},{"cond":{"i": true},"answer":"ABS_Idle"}]
            lemma abs_Idle_ref
            "M \<le> N \<Longrightarrow> i \<le> M \<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = Idle_ref M i"
            "M \<le> N \<Longrightarrow> i > M \<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = ABS_Idle M
            definition ABS_rules :: "nat \<Rightarrow> rule set" where [simp]:
            "ABS_rules M \<equiv>
            Trys M \<union> Crits M \<union> {ABS_Crit} \<union> Exits M \<union> Idle_refs M \<union> {ABS_Idle M} \<union> {chaos \<triangleright> skip}"

            definition ABS_rules' :: "nat \<Rightarrow> rule set" where [simp]:
            "ABS_rules' M \<equiv>
            ((Trys M) \<union> {chaos \<triangleright> skip}) \<union>
            ((Crits M) \<union> {ABS_Crit}) \<union>
            ((Exits M) \<union> {chaos \<triangleright> skip}) \<union>
            ((Idle_refs M) \<union> {ABS_Idle M})"

            lemma ABS_rules_eq_rules':
            "ABS_rules M = ABS_rules' M"
            by auto"'''
            absLemmas=[]
            unfolds=[ruleSet1.rule.name]
            for_abs_rules=[]
            tmpabsRuleDefList1=[]  #for definition of rule ABS_rules
            tmpabsRuleDefListM1=[] #for lemma abs_Idle_refs
            for absItem in item["abstract"]:
                cond=absItem["cond"]
                assms=[isabelle.Op("<=",isabelle.Const("M"),isabelle.Const("N")) ]
                abstracted=False
                absPars=[]
                leftPars=[]
                citems=sorted(cond.items(), key=lambda x:x[0])
                for k, val0 in citems:
                    leftPars.append(isabelle.Const(k))
                    if val0:# and k!="d":
                        isaCond0=isabelle.Op("<=",isabelle.Const(k),isabelle.Const("M"))   
                        absPars.append(isabelle.Const(k))  
                                    
                    else:
                        isaCond0=isabelle.Op(">",isabelle.Const(k),isabelle.Const("M"))
                        abstracted=True
                    if (k!="d"):assms.append(isaCond0)
                    else: pass
                arg1=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
                arg2=isabelle.Const("M")
                hasNList=[isabelle.Const("N")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
                arg3=isabelle.Fun(isabelle.Const(ruleSet1.rule.name),hasNList+leftPars) if item["ruleset"]!=item["answer"] else \
                    isabelle.Fun(isabelle.Const(item["ruleset"]),hasNList+leftPars)
                hasMList=[isabelle.Const("M")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
                if abstracted and absItem["answer"]!="skipRule":
                    thisAbstractr=prot.abs_rule_map[absItem["answer"]]
                    thisAbstractr=thisAbstractr.rule if isinstance(thisAbstractr,murphi.MurphiRuleSet) else thisAbstractr
                    absRuleHasNList=[isabelle.Const("N")] if hasParamExpr(thisAbstractr.cond) or any(hasParamCmd(c) for c in thisAbstractr.cmds) else [] 
                    absRuleHasMList=[isabelle.Const("M")] if hasParamExpr(thisAbstractr.cond) or any(hasParamCmd(c) for c in thisAbstractr.cmds) else [] 
                    
                else:
                    absRuleHasNList=[]   
                    absRuleHasMList=[]
                declVars=list(map(lambda x:x[0],cond.items()))
                print("------declVars:")
                for k in declVars:
                    print(k)
                print("------absPars:")
                for k in absPars:
                    print(k)
                print("------"+absItem["answer"])
                if "d" in absPars:
                    absPars.remove("d")
                else:
                    pass
                absRulesPred=isabelle.Set(isabelle.Const("skipRule")) if (absItem["answer"]=="skipRule") else \
                    isabelle.Set(isabelle.Fun(isabelle.Const(absItem["answer"]),absRuleHasNList)) if (absPars==[] and not("d" in declVars)) else \
                    isabelle.Set(isabelle.Fun(isabelle.Const(absItem["answer"]),[isabelle.Const("D")]+absRuleHasNList)) if absPars==[] else\
                    isabelle.Fun(isabelle.Const("oneParamCons"),[isabelle.Const("N"),isabelle.Const(absItem["answer"])])  if not("d" in declVars) else\
                    isabelle.Fun(isabelle.Const("oneParamCons"),[isabelle.Const("D"),isabelle.Fun(isabelle.Const(absItem["answer"]),[isabelle.Const("N")])])
                
                right=isabelle.Fun(isabelle.Const(absItem["answer"]),absRuleHasMList+absPars) if (absItem["answer"]!="skipRule") and abstracted else \
                    isabelle.Fun(isabelle.Const(absItem["answer"]),hasMList+absPars) if (absItem["answer"]!="skipRule") else \
                    isabelle.Const("skipRule") #if abstracted&(absItem["answer"]=="skip") else 
                    #isabelle.Fun(isabelle.Const(ruleSet1.rule.name),[isabelle.Const("M")]+absPars)''' #if abstracted&item["ruleset"]!=item["answer"] \
                conclusion=isabelle.eq(isabelle.Fun(isabelle.Const("absTransfRule"),[arg1,arg2,arg3]),right)

                typ=isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule)) if   not("d" in declVars) else\
                isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule)))
                defOfabsRule=isabelle.Definition(name=absItem["answer"]+"s",typ=typ, \
                val=absRulesPred,args=["N"] ) if not("d" in declVars) else\
                isabelle.Definition(name=absItem["answer"]+"s",typ=isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule)), \
                val=absRulesPred,args=["D","N"] )
                print(defOfabsRule.export())

                if absItem["answer"].startswith("ABS_"):
                    if not("d" in declVars):
                        thisPara1= absRuleHasNList
                    else:
                        thisPara1= [isabelle.Const("D")]+absRuleHasNList
                else:
                    if not("d" in declVars):
                        thisPara1=[isabelle.Const("N")]
                    else:
                         thisPara1= [isabelle.Const("D"),isabelle.Const("N")]
                absRulesPredForAbsRules=isabelle.Fun(isabelle.Const(absItem["answer"]+"s"),thisPara1)  if (absItem["answer"]!="skipRule") else \
                    isabelle.Set(isabelle.Const("skipRule"))
                if (absItem["answer"]!="skipRule")&abstracted:
                    pass#defOfabsRules.append(defOfabsRule)
                if (absItem["answer"]!="skipRule"):
                    absRuleDefList.append(absRulesPredForAbsRules)
                tmpabsRuleDefList1.append(absRulesPredForAbsRules)
                if absItem["answer"].startswith("ABS_"):
                    thisPara= absRuleHasMList
                else:
                    thisPara=[isabelle.Const("M")]
                absRulesPredForAbsRulesM=isabelle.Fun(isabelle.Const(absItem["answer"]+"s"),thisPara)  if (absItem["answer"]!="skipRule") and not("d" in vars) else \
                    isabelle.Fun(isabelle.Const(absItem["answer"]+"s"),[isabelle.Const("D")]+thisPara) if (absItem["answer"]!="skipRule") else \
                        isabelle.Set(isabelle.Const("skipRule"))
                tmpabsRuleDefListM1.append(absRulesPredForAbsRulesM)
                absLemmas.append(isabelle.isabelleLemma(assms=assms,conclusion=conclusion,inLemmas=True))
                
                #for_abs_rules1.append(right)
                #for_abs_rules1.append(right)
                #unfolds=([ruleSet1.rule.name] if item["ruleset"]!=item["answer"] else [])+[absItem["answer"]]
                unfolds.append(absItem["answer"])
            absRuleDefList1.append(isabelle.Tuple(isabelle.UN(tmpabsRuleDefList1)))
            simpadds=["Let_def"]
            absLemma=isabelle.isabelleLemmas(name="abs_"+ruleSet1.rule.name,lemmas=absLemmas,proof=[isabelle.autoProof(unfolds=unfolds,simpadds=simpadds)])
            res.append(absLemma)
            absAllLemmaOnItemAssm=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
            if (len(chooseNodeDecls(ruleSet1.var_decls))==2):
                print(ruleSet1.__str__())
                swapListEle(tmpabsRuleDefListM1,1,2)

            absAllLemmaOnItemPred=isabelle.eq(isabelle.Op("`", \
            isabelle.Fun(isabelle.Const("absTransfRule"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), \
            isabelle.Const("M")]),isabelle.Fun(isabelle.Const(ruleSet1.rule.name+"s"),[isabelle.Const("N")])), \
                isabelle.Tuple(isabelle.UNLeft(tmpabsRuleDefListM1))) if (not "d" in vars) else\
            isabelle.eq(isabelle.Op("`", \
            isabelle.Fun(isabelle.Const("absTransfRule"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), \
            isabelle.Const("M")]),isabelle.Fun(isabelle.Const(ruleSet1.rule.name+"s"),[isabelle.Const("D"),isabelle.Const("N")])), \
                isabelle.Tuple(isabelle.UNLeft(tmpabsRuleDefListM1)))    
            thisUnfolds=[None if isinstance(k,isabelle.Set) else k.fun.name for k in tmpabsRuleDefListM1]
            if None in thisUnfolds:
                thisUnfolds.remove(None)
            absLemmasOnSetItemProof=isabelle.IsabelleApplyRuleProof(name="absGen",unfolds=thisUnfolds) if len(ruleSet1.var_decls)==1 else\
                isabelle.IsabelleApplyRuleProof(name="absGen2",unfolds=thisUnfolds) if len(ruleSet1.var_decls)==1 and ("D" in list(map(lambda x:x.name,ruleSet1.var_decls))) else\
                isabelle.IsabelleApplyRuleProof(name="absGenDd",unfolds=thisUnfolds+["oneParamCons"])
            absLemmasOnSetItem=isabelle.isabelleLemma(name="Abs_"+ruleSet1.rule.name+"s", assms=[absAllLemmaOnItemAssm], conclusion=absAllLemmaOnItemPred, \
                proof=[absLemmasOnSetItemProof,isabelle.autoProof(usings=["abs_"+ruleSet1.rule.name])]) 
            absLemmasOnSets.append(absLemmasOnSetItem)
            passName=oldRuleName
        #absRuleDefList.extend(for_abs_rules)
        #absRuleDefList1.extend(for_abs_rules1)
        except (KeyError):
            # print(item)
            # print("exception%s\n"%item["rule"])
            rule=prot.ori_rule_map[item["rule"]]
            vars = []
            hasForall=False
            if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds):
                vars.append("N")
                hasForall=True
            '''for var_decl in rule.var_decls:
                vars.append(var_decl.name)'''
            paraNums=len(vars) - 1 if hasForall else len(vars)
            args=list(map(lambda a: isabelle.Const(a),vars))
            ruleConst=isabelle.Const(rule.name)
            #generate definition for strengthening lemmas for this rule
            typ = isabelle.FunType(isabelle.nat, isabelle.ListType(isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.formula))))
            #val=isabelle.List(tuple(map(lambda lemma:isabelle.Fun(isabelle.Const(lemma), [isabelle.Const("N")]),item["strengthen"])))
            # print(type(tuple(isabelle.Fun(isabelle.Const(lemma), [isabelle.Const("N")]) for lemma in item["strengthen"])))
            val=isabelle.List(*tuple(isabelle.Fun(isabelle.Const(lemma+"'"), [isabelle.Const("N")]) for lemma in item["strengthen"]))
            #val=[] #isabelle.List(*tuple(isabelle.Fun(isabelle.Const(lemma), [isabelle.Const("N")]) for lemma in item["strengthen"])) 
            defLemma=isabelle.Definition(name="lemmasFor_"+rule.name, \
            typ=typ, val=val,args=["N"])
            ruleInst=isabelle.Fun(isabelle.Const(rule.name),args) #if args==[] else isabelle.Fun(isabelle.Const("wellFormedRule"),[isabelle.Const("N") ]) #isabelle.Const(def_name) if args==[] else  
            #generate r_ref

            #ruleSet1=ruleset
            r_ref=murphi.MurphiRule(name=rule.name+"_ref",cond=rule.cond,cmds=rule.cmds)
            '''for lemma in item["strengthen"]:
                lemmaC=prot.lemma_map[lemma].inv
                r_ref=abstract.strengthen(r_ref,lemmaC)'''
            oldRuleName=rule.name
            #r_ref.name=ruleset.rule.name+"_ref"
            #ruleSet1=murphi.MurphiRuleSet(var_decls=ruleset.var_decls,rule=r_ref)
            #print("test ruleset.rule.name=%s"%ruleset.rule.name)
            #generate lemmas on r_strengthen
            oldhasNList=[isabelle.Const("N")] if hasParamExpr(r_ref.cond) or any(hasParamCmd(c) for c in  r_ref.cmds) else []
        
            hasNList=[isabelle.Const("N")] if hasParamExpr (r_ref.cond) or any(hasParamCmd(c) for c in  r_ref.cmds) else []
            
            '''left1=isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("j"),isabelle.Const("i")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList+[isabelle.Const("i")]) \
                ]) if (paraNums==1) else \
                isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("i"),isabelle.Const("j")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList+[isabelle.Const("i"),isabelle.Const("j")]) \
                ])  '''

            left1=isabelle.Fun(isabelle.Const("strengthenRuleByFrmL2"), [\
                isabelle.Fun(isabelle.Const("map2'"),[isabelle.Fun(isabelle.Const("lemmasFor_"+oldRuleName),[isabelle.Const("N")]),isabelle.Const("j"),isabelle.Const("i")]), \
                isabelle.Fun(isabelle.Const(oldRuleName), oldhasNList)])
                
            right1=isabelle.Fun(isabelle.Const(r_ref.name),hasNList)
            eq1=isabelle.eq(left1,right1)
            lemmas_def=" ".join(lemma+"_def" for lemma in item["strengthen"])
            proof=isabelle.autoProof(unfolds=[("lemmasFor_%s_def %s %s_def %s_ref")%(oldRuleName,lemmas_def,oldRuleName,oldRuleName)])
            lemma1= isabelle.isabelleLemma(name=oldRuleName+"_strengthen",assms=[], conclusion=eq1,proof=[proof]) 
            #generate lemmas on r_StrengthRel
            pred2=isabelle.Fun(isabelle.Const("strengthenRel"), [ \
                isabelle.Fun(isabelle.Const(oldRuleName+"s"),oldhasNList), \
                isabelle.Fun(isabelle.Const("set"), [isabelle.Fun(isabelle.Const("InvS"),[isabelle.Const("N")])]), \
                isabelle.Fun(isabelle.Const(oldRuleName+"_refs"), oldhasNList),
                isabelle.Const("N") \
                ])
            proof21=isabelle.blastProof(usings=["strengthenRefl"], unfolds=["%ss_def %s_refs_def %s_def %s_ref"%(oldRuleName,oldRuleName,oldRuleName,oldRuleName)])
            '''rule_tac="?lemmasFor_r=\"lemmasFor_"+oldRuleName+"\"")
            proof22=isabelle.presburgerProof(usings=[oldRuleName+"_strengthen"])
            proof23=isabelle.blastProof(unfolds=["InvS"])'''
            lemma2=isabelle.isabelleLemma(name=oldRuleName+"StrengthRel",assms=[], conclusion=pred2,proof=[proof21]) 
            predOfLemma=isabelle.Fun(isabelle.Const(("lemmasFor_%s"%oldRuleName)),[isabelle.Const("N")])
            predOfLemma1=isabelle.Fun(isabelle.Const(("lemmasFor_%s"%oldRuleName+"'")),[isabelle.Const("N")])
            
            #abstract r_ref
            absRule=[]
            absRules=[]
            suffix=""
            '''if isinstance(ruleSet1,murphi.MurphiRuleSet):
                limits=dict()
                if len(ruleSet1.var_decls)==1:
                    limits[ruleSet1.var_decls[0].name]=False
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    if absr!=ruleSet1.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
                        absRule.append(absr)

                elif len(ruleSet1.var_decls)==2:
                    limits[ruleSet1.var_decls[0].name]=False
                    limits[ruleSet1.var_decls[1].name]=True
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    absrulesetdecls=ruleSet1.var_decls[1:2]
                    if absr!=ruleSet1.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)
                        absRules.append(absr)

                    limits=dict()
                    limits[ruleSet1.var_decls[1].name]=False
                    limits[ruleSet1.var_decls[0].name]=True
                    absr=abstract.absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    absrulesetdecls=ruleSet1.var_decls[0:1]
                    if absr!=ruleSet1.rule and absr!=None:
                        absruleset=murphi.MurphiRuleSet(absrulesetdecls,absr)
                        prot.abs_rule_map[absr.name]=absruleset
                        prot.decls.append(absruleset)
                        absRules.append(absr)
                    limits=dict()
                    limits[ruleSet1.var_decls[0].name]=False
                    limits[ruleSet1.var_decls[1].name]=False
                    absr=absTransfRule(ruleSet1.rule, limits, suffix=suffix)
                    if absr!=ruleSet1.rule and absr!=None:
                        prot.abs_rule_map[absr.name]=absr
                        prot.decls.append(absr)
                        absRule.append(absr)'''
            def11,lemma11,lemma21,term11,unfolds1,usings1=translateRule1(r_ref)
            deriveAllLLemmaist.append(lemma11)
            symProtAllLemmaList.append(lemma21)
            dsymProtAllLemmaList.append(dlemma21)
            refRulesDefList.append(term11)
            deriveAllLLemmaProofUnfolds1.extend(unfolds1)
            symProtAllLemmaProofUsings2.extend(usings1)

            InvSList.append(predOfLemma)
            InvS1List.append(predOfLemma1)
            res.append(defLemma)
            '''res.append(translateRuleSet(ruleSet1))'''
            
            res.append(translateRule(r_ref))
            res.append(genRuleSymLemma(r_ref))
            res.append(def11)
            res.append(lemma1)
            res1.append(lemma2)
            
            '''for absr in absRules:
                res.append(translateRuleSet(absr))
                defA,lemmaA1,lemmaA2,termA,unfoldsA,usingsA=translateRuleSets(absr)
                res.append(defA)'''
            '''generate1. lemmas on abstraction for r_refs by json:
            2. definitions for    ABS_rules,  ABS_rules' 
            "abstract":[{"cond":{"i": false},"answer":"ABS_Idle"},{"cond":{"i": true},"answer":"ABS_Idle"}]
            lemma abs_Idle_ref
            "M \<le> N \<Longrightarrow> i \<le> M \<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = Idle_ref M i"
            "M \<le> N \<Longrightarrow> i > M \<Longrightarrow> absTransfRule (env N) M (Idle_ref N i) = ABS_Idle M
            definition ABS_rules :: "nat \<Rightarrow> rule set" where [simp]:
            "ABS_rules M \<equiv>
            Trys M \<union> Crits M \<union> {ABS_Crit} \<union> Exits M \<union> Idle_refs M \<union> {ABS_Idle M} \<union> {chaos \<triangleright> skip}"

            definition ABS_rules' :: "nat \<Rightarrow> rule set" where [simp]:
            "ABS_rules' M \<equiv>
            ((Trys M) \<union> {chaos \<triangleright> skip}) \<union>
            ((Crits M) \<union> {ABS_Crit}) \<union>
            ((Exits M) \<union> {chaos \<triangleright> skip}) \<union>
            ((Idle_refs M) \<union> {ABS_Idle M})"

            lemma ABS_rules_eq_rules':
            "ABS_rules M = ABS_rules' M"
            by auto"'''
            absLemmas=[]
            unfolds=[r_ref.name]
            for_abs_rules=[]
            tmpabsRuleDefList1=[]  #for definition of rule ABS_rules
            tmpabsRuleDefListM1=[] #for lemma abs_Idle_refs
            hasNList=[isabelle.Const("N")] if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds) else []
            hasMList=[isabelle.Const("M")] if hasParamExpr(rule.cond) or any(hasParamCmd(c) for c in rule.cmds) else []

            absRulesPred=isabelle.Set(isabelle.Const(r_ref.name))
            right=isabelle.Fun(isabelle.Const(r_ref.name),hasMList) if not("d" in vars) else\
            isabelle.Fun(isabelle.Const(r_ref.name),[isabelle.Const("D")]+hasMList)
            arg1=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
            arg2=isabelle.Const("M")
            arg3=isabelle.Fun(isabelle.Const(r_ref.name),hasMList) 
            conclusion=isabelle.eq(isabelle.Fun(isabelle.Const("absTransfRule"),[arg1,arg2,arg3]),right)
            #defOfabsRule=isabelle.Definition(name=rule.name+"s",typ=isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule)), val=absRulesPred,args=["N"] )

                
            absRulesPredForAbsRules=(isabelle.Fun(isabelle.Const(r_ref.name+"s"),hasNList)) if not("d" in vars) else\
            isabelle.Fun(isabelle.Const(r_ref.name+"s"),[isabelle.Const("D")]+hasNList)
            '''if (absItem["answer"]!="skipRule")&abstracted:
                    defOfabsRules.append(defOfabsRule)
            if (absItem["answer"]!="skipRule"):
                    absRuleDefList.append(absRulesPredForAbsRules)'''
            absRuleDefList.append(absRulesPredForAbsRules)
            
            tmpabsRuleDefList1.append(absRulesPredForAbsRules)

            absRulesPredForAbsRulesM=isabelle.Fun(isabelle.Const(r_ref.name+"s"),hasMList) if not("d" in vars) else\
            isabelle.Fun(isabelle.Const(r_ref.name+"s"),[isabelle.Const("D")]+hasMList)

            '''absRulesPredForAbsRulesM=isabelle.Fun(isabelle.Const(absItem["answer"]+"s"),[isabelle.Const("M")])  if (absItem["answer"]!="skipRule") else \
                    isabelle.Set(isabelle.Const("skipRule"))'''
            tmpabsRuleDefListM1.append(absRulesPredForAbsRulesM)
            assms=[isabelle.Op("<=",isabelle.Const("M"),isabelle.Const("N")) ]
            absLemmas.append(isabelle.isabelleLemma(assms=assms,conclusion=conclusion,inLemmas=True))
                
                #for_abs_rules1.append(right)
                #for_abs_rules1.append(right)
                #unfolds=([ruleSet1.rule.name] if item["ruleset"]!=item["answer"] else [])+[absItem["answer"]]
            unfolds.append(absItem["answer"])

            #tmpabsRuleDefList1
            '''for absItem in item["abstract"]:
                cond=absItem["cond"]
                assms=[isabelle.Op("<=",isabelle.Const("M"),isabelle.Const("N")) ]
                abstracted=False
                absPars=[]
                leftPars=[]
                for k, val0 in cond.items():
                    leftPars.append(isabelle.Const(k))
                    if val0:
                        isaCond0=isabelle.Op("<=",isabelle.Const(k),isabelle.Const("M"))   
                        absPars.append(isabelle.Const(k))  
                                    
                    else:
                        isaCond0=isabelle.Op(">",isabelle.Const(k),isabelle.Const("M"))
                        abstracted=True
                    assms.append(isaCond0)
                arg1=isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")])
                arg2=isabelle.Const("M")
                hasNList=[isabelle.Const("N")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
                arg3=isabelle.Fun(isabelle.Const(ruleSet1.rule.name),hasNList+leftPars) if item["ruleset"]!=item["answer"] else \
                    isabelle.Fun(isabelle.Const(item["ruleset"]),hasNList+leftPars)
                hasMList=[isabelle.Const("M")] if hasParamExpr(ruleSet1.rule.cond) or any(hasParamCmd(c) for c in ruleSet1.rule.cmds) else []
                if abstracted and absItem["answer"]!="skipRule":
                    thisAbstractr=prot.abs_rule_map[absItem["answer"]]
                    thisAbstractr=thisAbstractr.rule if isinstance(thisAbstractr,murphi.MurphiRuleSet) else thisAbstractr
                    absRuleHasNList=[isabelle.Const("N")] if hasParamExpr(thisAbstractr.cond) or any(hasParamCmd(c) for c in thisAbstractr.cmds) else [] 
                    absRuleHasMList=[isabelle.Const("M")] if hasParamExpr(thisAbstractr.cond) or any(hasParamCmd(c) for c in thisAbstractr.cmds) else [] 
                    
                else:
                    absRuleHasNList=[]   
                    absRuleHasMList=[]

                absRulesPred=isabelle.Set(isabelle.Const("skipRule")) if (absItem["answer"]=="skipRule") else \
                    isabelle.Set(isabelle.Fun(isabelle.Const(absItem["answer"]),absRuleHasNList)) if absPars==[] else \
                    isabelle.Fun(isabelle.Const("oneParamCons"),[isabelle.Const("N"),isabelle.Const(absItem["answer"])])  
                
                right=isabelle.Fun(isabelle.Const(absItem["answer"]),absRuleHasMList+absPars) if (absItem["answer"]!="skipRule") and abstracted else \
                    isabelle.Fun(isabelle.Const(absItem["answer"]),hasMList+absPars) if (absItem["answer"]!="skipRule") else \
                    isabelle.Const("skipRule") #if abstracted&(absItem["answer"]=="skip") else 
                    #isabelle.Fun(isabelle.Const(ruleSet1.rule.name),[isabelle.Const("M")]+absPars) #if abstracted&item["ruleset"]!=item["answer"] \
                conclusion=isabelle.eq(isabelle.Fun(isabelle.Const("absTransfRule"),[arg1,arg2,arg3]),right)

                
                defOfabsRule=isabelle.Definition(name=absItem["answer"]+"s",typ=isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule)), \
                val=absRulesPred,args=["N"] )

                
                absRulesPredForAbsRules=isabelle.Fun(isabelle.Const(absItem["answer"]+"s"),[isabelle.Const("N")])  if (absItem["answer"]!="skipRule") else \
                    isabelle.Set(isabelle.Const("skipRule"))
                if (absItem["answer"]!="skipRule")&abstracted:
                    defOfabsRules.append(defOfabsRule)
                if (absItem["answer"]!="skipRule"):
                    absRuleDefList.append(absRulesPredForAbsRules)
                tmpabsRuleDefList1.append(absRulesPredForAbsRules)
                absRulesPredForAbsRulesM=isabelle.Fun(isabelle.Const(absItem["answer"]+"s"),[isabelle.Const("M")])  if (absItem["answer"]!="skipRule") else \
                    isabelle.Set(isabelle.Const("skipRule"))
                tmpabsRuleDefListM1.append(absRulesPredForAbsRulesM)
                absLemmas.append(isabelle.isabelleLemma(assms=assms,conclusion=conclusion,inLemmas=True))
                
                #for_abs_rules1.append(right)
                #for_abs_rules1.append(right)
                #unfolds=([ruleSet1.rule.name] if item["ruleset"]!=item["answer"] else [])+[absItem["answer"]]
                unfolds.append(absItem["answer"])'''
            absRuleDefList1.append(isabelle.Tuple(isabelle.UN(tmpabsRuleDefList1)))
            simpadds=["Let_def"]
            absLemma=isabelle.isabelleLemmas(name="abs_"+rule.name,lemmas=absLemmas,proof=[isabelle.autoProof(unfolds=unfolds, simpadds=simpadds)])
            res.append(absLemma)
            absAllLemmaOnItemAssm=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
            absAllLemmaOnItemPred=isabelle.eq(isabelle.Op("`", \
            isabelle.Fun(isabelle.Const("absTransfRule"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), \
            isabelle.Const("M")]),isabelle.Fun(isabelle.Const(r_ref.name+"s"),hasNList)), \
                absRulesPredForAbsRulesM )
            thisUnfolds=[None if isinstance(k,isabelle.Set) else k.fun.name for k in tmpabsRuleDefListM1]
            if None in thisUnfolds:
                thisUnfolds.remove(None)
            absLemmasOnSetItemProof=isabelle.IsabelleApplyRuleProof(name="absGen",unfolds=thisUnfolds)
            absLemmasOnSetItem=isabelle.isabelleLemma(name="Abs_"+rule.name+"s", assms=[absAllLemmaOnItemAssm], conclusion=absAllLemmaOnItemPred, \
                proof=[isabelle.autoProof(unfolds=[r_ref.name+"s", r_ref.name])]) 
            absLemmasOnSets.append(absLemmasOnSetItem)
            passName=rule.name
        #absRuleDefList.extend(for_abs_rules)
        #absRuleDefList1.extend(for_abs_rules1)

    predOfInvS=isabelle.List(*(InvSList))
    oneLemmasType=isabelle.ListType(isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.formula)))
    typeOfInvS=isabelle.FunType(isabelle.nat,isabelle.ListType(oneLemmasType))
    defOfInvS=isabelle.Definition(name="InvS",typ=typeOfInvS,args=["N"],val=predOfInvS)
    res.append(defOfInvS)
    predOfInvS1=isabelle.List(*(InvS1List))
    defOfInvS1=isabelle.Definition(name="InvS'",typ=typeOfInvS,args=["N"],val=predOfInvS1)
    #res.append(defOfInvS1)
    deriveAllLLemmaProof=[isabelle.autoProof(unfolds=["deriveRule_def deriveForm_def deriveStmt"] \
        +deriveAllLLemmaProofUnfolds1)]
    symProtAllLemmaProof=[isabelle.autoProof(usings=symProtAllLemmaProofUsings2+["symParaRuleInfSymRuleSet","symParaRuleInfSymRuleSet2","DIsymParaRuleInfSymRuleSet"])]
    deriveAllLLemmas=isabelle.isabelleLemmas("deriveAllRef",deriveAllLLemmaist,proof=deriveAllLLemmaProof)
    symProtAllLemmas=isabelle.isabelleLemmas("symProtAllRef",symProtAllLemmaList,proof=symProtAllLemmaProof)
    res1.append(deriveAllLLemmas)
    res1.append(symProtAllLemmas)
    typ = isabelle.FunType(isabelle.nat, isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule)))
    
    def_ref_rules=isabelle.Definition(name="rule_refs",typ=typ,val=isabelle.UN(refRulesDefList),args=["D","N"])
    res.append(def_ref_rules)
    lenOfSpec=len(strengthenSpec)
    pred2=isabelle.Fun(isabelle.Const("strengthenRel"), [ \
              isabelle.Fun(isabelle.Const("rules"),[isabelle.Const("D"),isabelle.Const("N")]), \
              isabelle.Fun(isabelle.Const("set"), [isabelle.Fun(isabelle.Const("InvS"),[isabelle.Const("N")])]), \
              isabelle.Fun(isabelle.Const("rule_refs"), [isabelle.Const("D"),isabelle.Const("N")]),
              isabelle.Const("N") \
              ])
    proof21=isabelle.IsabelleApplyRuleProof(name="strenRelUnion",unfolds=["rules", "rule_refs"])
    proof22s=[
        [isabelle.blastProof(introITag="intro:",intros=["%sStrengthRel"%(getRuleOrRuleset(item))]),
        isabelle.IsabelleApplyRuleProof(name="strenRelUnion" )]
        for item in strengthenSpec[0:(lenOfSpec-2)]]

    proofs=[a for ele in proof22s for a in ele]
    lastProofs=[isabelle.blastProof(introITag="intro:", \
    intros=["%sStrengthRel"%(item["ruleset"])]) \
        for item in strengthenSpec[lenOfSpec -2:(lenOfSpec)]]
    #test=(print ("%sStrengthRel"%(item["ruleset"]))  for item in strengthenSpec)
    lemma2=isabelle.isabelleLemma(name="StrengthRelRules2Rule_refs",assms=[], conclusion=pred2,
    proof=[proof21]+proofs+lastProofs) 
    res1.append(lemma2) 
    absRuleDefList.append(isabelle.Set(isabelle.Const("skipRule")))
    absRuleSetPred=isabelle.UN(absRuleDefList)
    absRuleDef=isabelle.Definition(name="ABS_rules",typ=isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule))), \
            val=absRuleSetPred,args=["D","N"],is_simp=True  )  
    
    dsymProtAllLemmaPredList=list(map(lambda x: isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"),x ]), absRuleDefList))
    dsymProtAllLemmaList=list(map(lambda x: isabelle.isabelleLemma(assms=[],conclusion=x,inLemmas=True),dsymProtAllLemmaPredList))
    
    #dsymProtAllLemmaPredList=list(map(lambda x: isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"),x ]), absRuleDefList))
    dsymProtAllLemmaProof=list(map(lambda x: toProof(x), absRuleDefList))
    dsymProtAll=isabelle.isabelleLemmas(name="DsymProtAllRef",lemmas=dsymProtAllLemmaList,\
                                        proof=[item for sublist in dsymProtAllLemmaProof for item in sublist])
    
    res1.append(dsymProtAll) 
    dabsTransferRules=list(map(lambda x: toDabsRuleLemma(x), absRuleDefList))
    toKeepDataLemmas=list(map(lambda x:toKeepDataLemma(x),absRuleDefList))
    for k in dabsTransferRules:
        res1.append(k)
    for k in toKeepDataLemmas:
        res1.append(k)
    absRuleSetPred1=isabelle.UN(absRuleDefList1)
    absRuleDef1=isabelle.Definition(name="ABS_rules'",typ=isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.setType(isabelle.rule))), \
            val=absRuleSetPred1,args=["D","N"],is_simp=True )  #ABS_rules':absRuleDef1<-absRuleSetPred1<-absRuleDefList1<-tmpabsRuleDefList1<-absRulesPredForAbsRules
    ABS_rules_eqLemmaCon=isabelle.eq(isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("ABS_rules'"),[isabelle.Const("D"),isabelle.Const("M")]))
    ABS_rules_eqLemma=isabelle.isabelleLemma(name="ABS_rules_eq_rules'", assms=[], \
    conclusion=ABS_rules_eqLemmaCon,proof=[isabelle.autoProof()]) 
    absAllLemmaAssm=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
    absAllLemmaPred=isabelle.eq(isabelle.Op("`", \
        isabelle.Fun(isabelle.Const("absTransfRule"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), \
        isabelle.Const("M")]),isabelle.Fun(isabelle.Const("rule_refs"),[isabelle.Const("D"),isabelle.Const("N")])), \
             isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("M")]))
    proof1=isabelle.substProof(name="ABS_rules_eq_rules'")
    proof2=isabelle.introProof(unfolds=["rule_refs", "ABS_rules'"],intros=["image_UnI"])
    ruleNames3=getAllProtRuleNames()
    ruleNames3=["Abs_"+k+"s" for  k in ruleNames3]
    ruleNames31=getAllProtRuleSetNames()
    ruleNames31=["Abs_"+k+"_refs" for  k in ruleNames31]
    proof3=isabelle.autoProof(simpadds=ruleNames3+ruleNames31)
    absAllLemma=isabelle.isabelleLemma(name="ABS_all",assms=[absAllLemmaAssm],conclusion=absAllLemmaPred,proof= \
        [proof1,proof2,proof3])
    DabsAllLemmaAssm=isabelle.Op("<",isabelle.Const("0"),isabelle.Const("D"))
    
    DabsAllLemmaPred=isabelle.eq(isabelle.Op("`", \
        isabelle.Fun(isabelle.Const("DabsTransfRule"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), \
        ]),isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("N")])), \
             isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("1"),isabelle.Const("N")]))
    proof1=isabelle.substProof(name="ABS_rules_eq_rules'")
    proof11=isabelle.substProof(name="ABS_rules_eq_rules'")
    proof2=isabelle.introProof(unfolds=["ABS_rules'"],intros=["image_UnI"])
    #ruleNames3=getAllProtRuleNames()
    #ruleNames3=["DAbs_"+k+"s" for  k in ruleNames3]
    ruleNames31=list(map(lambda x:"skipRuleSet" if isinstance(x,isabelle.Set) else x.fun.name, absRuleDefList))
    ruleNames31=["DAbs_"+k for  k in ruleNames31]
    proof3=isabelle.autoProof(usings=ruleNames31)
    dabsAllLemma=isabelle.isabelleLemma(name="DABS_all",assms=[DabsAllLemmaAssm],conclusion=DabsAllLemmaPred,\
        proof=[proof1,proof11,proof2,proof3])
    (resTmp,initSpecs)=translateStartState(prot)
    LemmaAllReachKeepData=genLemmaAllReachKeepData(absRuleDefList,initSpecs) 
    lemmaDwellFormLemma=genDwellFormLemma(absRuleDefList)
    print("-----defOfabsRules'slength-----"+str(defOfabsRules.__len__()))
    for k in defOfabsRules:
        print(k.export())
    return defOfabsRules+res+res1+absLemmasOnSets+[absRuleDef,absRuleDef1,ABS_rules_eqLemma,absAllLemma,dabsAllLemma,LemmaAllReachKeepData,lemmaDwellFormLemma]
'''
defOfabsRule is for one definition ABS_rs::"nat =>rule set"
defOfabsRules is a list of defOfabsRule.

lemma ABS_rules_eq_rules':
  "ABS_rules M = ABS_rules' M"
  by auto

lemma "strengthenRel (rules N)  (set (InvS N)) (rules2 N) N "
  apply(unfold rules_def rules2_def, (rule strenRelUnion)+)
  apply(blast intro: TryStrengthRel)
    apply(blast intro: CritStrengthRel)
   apply(blast intro:ExitStrengthRel)
  by(blast intro: IdleStrengthRel) 
  lemma ABS_all:
  "M < N ⟹ absTransfRule (env N) M ` rules2 N = ABS_rules M"
  apply (subst ABS_rules_eq_rules')
  unfolding rules2_def ABS_rules'_def
  apply (intro image_UnI) by auto
  '''

#genallLemmas'
def genAllInvariantsPrime(prot):
    res=[]
    unfoldsForsymInvsLemma=[]
    global lemmasForsymInvsLemma
    lemmasForsymInvsLemma=[]
    
    proofsForsymInvsLemma=[]
    for k,val in prot.lemma_map.items():
        extLemma=extMurphiInvariant(val)
        extLemma.test()
        res.append((extLemma.genLemma1()))
        res.append(extLemma.genabsTransfLemma() )
        res.append(extLemma.genstrengthenVsObsLemma())
        (name,lemma,proof)=extLemma.genSymInvsItem1()
        unfoldsForsymInvsLemma.append(name)
        lemmasForsymInvsLemma.append(lemma)
        proofsForsymInvsLemma.append(proof)
        res.append(extLemma.genSafeAndderiveForm())
        res.append(extLemma.genDsafeAndderiveForm())
        
#revised in 2024/4/26
    if len(lemmasForsymInvsLemma)!=0:
        res.append(isabelle.isabelleLemmas(name="symInvs",lemmas=lemmasForsymInvsLemma, \
        proof=[isabelle.autoProof(unfolds=unfoldsForsymInvsLemma)]+proofsForsymInvsLemma))
    
    return(res)


'''lemma wellFormedRules:
  "r \<in> rules N \<Longrightarrow> wellFormedRule (env N) N r"
  unfolding wellFormedRule.simps
  by (auto simp add: rules_def rules_simp
    symPI_Remote_Get
    ...
    
lemma absProtSim:
  assumes "M < N"
    and "M = 1"
    and "isAbstractProtInvSet absRules Is S' M env ""\<forall>i invL f s l. l\<le>1 \<and> invL \<in> set (InvS' N) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo {f'. \<exists>f. f \<in> (allInitSpecs N) \<and> f' = absTransfForm (env N) M f} (ABS_rules M) i s \<longrightarrow>
           formEval (absTransfForm (env N) M (f 0 l)) s"
    shows isParamProtInvSet  rs Is S N "\<forall>invL f s i j. invL \<in> set (InvS N) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo (allInitSpecs N) (rules N) k s \<longrightarrow>
           i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> formEval (f i j) s" 
  apply (rule_tac ?rs2.0 = "rules2 N" and env="env N" and S="set (InvS N)" and S'="set (InvS' N)" and M=M and absRules="ABS_rules M" in CMP1)
  subgoal for r'''
def primeLs(ls):
    return([n+"'" for n in ls])

def genAllRuleSetStuff(prot,str_data,initSpecs):
    nameOfLemmas1=[]
    for k, decl in prot.lemma_map.items():
        nameOfLemmas1.append(k+"'")
    namesOfRule=[]
    for k, decl in prot.ori_rule_map.items():
        namesOfRule.append(k)
    res=[]
    lemmasFor_List=[]
    InvSList1=[]
    nameOflemmasFors1=[]
    for item in str_data:# for k,val in prot._map.items():
        try:
            r=prot.ori_rule_map[item["ruleset"]]
            extRs=extMurphiRuleSet(r,item["strengthen"])
            #extLemma.test()
            res.append(extRs.genStrengthenLemmasDef1(item))
            res.append((extRs.genLemmastrengthenVsObsLs())) 
            res.append(extRs.genFitenvLemma())
            res.append(extRs.genSafeAndDeriveLemma(primeLs(item["strengthen"])))
            if ("lemmasFor_"+item["ruleset"]) not in lemmasFor_List:
                lemmasFor_List.append("lemmasFor_"+item["ruleset"])
            predOfLemma1=isabelle.Fun(isabelle.Const(("lemmasFor_%s"%item["ruleset"]+"'")),[isabelle.Const("N")])
            InvSList1.append(predOfLemma1)
        except (KeyError):
            r=prot.ori_rule_map[item["rule"]]
            extRs=extMurphiRule(r)
            #extLemma.test()
            res.append(extRs.genStrengthenLemmasDef1(item))
            res.append((extRs.genLemmastrengthenVsObsLs())) 
            res.append(extRs.genFitenvLemma())            
            res.append(extRs.genSafeAndDeriveLemma(primeLs(item["strengthen"])))
            if ("lemmasFor_"+item["rule"]) not in lemmasFor_List:
                lemmasFor_List.append("lemmasFor_"+item["rule"])
            predOfLemma1=isabelle.Fun(isabelle.Const(("lemmasFor_%s"%item["rule"]+"'")),[isabelle.Const("N")])
            InvSList1.append(predOfLemma1)
         
        #nameOflemmasFors()
    

    nameOflemmasFors1=[n+"'" for n in lemmasFor_List]
    predOfInvS1=isabelle.List(*(InvSList1))
    oneLemmasType=isabelle.ListType(isabelle.FunType(isabelle.nat,isabelle.FunType(isabelle.nat,isabelle.formula)))
    typeOfInvS=isabelle.FunType(isabelle.nat,isabelle.ListType(oneLemmasType))
    defOfInvS1=isabelle.Definition(name="InvS'",typ=typeOfInvS,args=["N"],val=predOfInvS1)
    res.append(defOfInvS1)
    
    assms=[isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const("rule_refs"),[isabelle.Const("D"),isabelle.Const("N")]))]   
    conclusion=isabelle.Fun(isabelle.Const("wellFormedRule") ,[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),isabelle.Const("N"),isabelle.Const("r")])
    #funr=lambda r.name if (isinstance(r,murphi.murphi.MurphiRule)) else r.rule.name
    simpOnSymRules1=list(r+"_refs_def" for r in prot.ori_rule_map.keys())
    simpOnSymRules2=list("sym"+r+"_ref" for r in prot.ori_rule_map.keys())
    proof=isabelle.autoProof(simpadds=["rule_refs_def  "]+simpOnSymRules1+simpOnSymRules2)
    res.append(isabelle.isabelleLemma(name="wellFormedRule_refs",assms=assms,conclusion=conclusion,proof=[proof]))
    
    '''lemma SafeAndderiveCLemmas : 
                  "[|M < N;M = 1;l <= 1; pinvL: set (InvS' N); pf : set pinvL; l≤ 1 
     |] 
                 ==> safeForm (env N) M (pf 0 l) & deriveForm (env N) (pf  0 l)"
    unfolding InvS'_def lemmasFor_Try'_def lemmasFor_Crit'_def lemmasFor_Idle'_def lemmasFor_Exit'_def
    using SafeAndderiveFormLemma_1 apply(auto      )    
 
    done'''
    cond1=isabelle.Op("<",isabelle.Const("M"),isabelle.Const("N"))
    cond2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
    cond3=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("M"))
    cond31=isabelle.Op("<=",isabelle.Const("k"),isabelle.Const("M"))
    cond4=isabelle.Op(":",isabelle.Const("pinvL"),isabelle.Fun(isabelle.Const("set"),[(isabelle.Fun(isabelle.Const("InvS'"),[isabelle.Const("N")]))]))
    cond5=isabelle.Op(":",isabelle.Const("pf"),isabelle.Fun(isabelle.Const("set"),[isabelle.Const("pinvL")]))
    pred1=isabelle.Fun(isabelle.Const("safeForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("M"), \
            isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
    pred2=isabelle.Fun(isabelle.Const("deriveForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),   \
            isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
    unfolds=["InvS'"]+nameOflemmasFors1
    usings=["SafeAndderiveForm"+n for n in nameOfLemmas1]
    #usings=["SafeAndDerive"+n for n in namesOfRule]
    res.append(isabelle.isabelleLemma(assms=[cond1,cond2,cond3,cond31,cond4,cond5], \

            conclusion=isabelle.Op("&",pred1,pred2),name="SafeAndderiveAll", \
            proof=[isabelle.autoProof(unfolds=unfolds,usings=usings)]))
    dpred1=isabelle.Fun(isabelle.Const("DsafeForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("M"), \
            isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
    dpred2=isabelle.Fun(isabelle.Const("deriveForm"), \
            [isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),   \
            isabelle.Fun(isabelle.Const("pf"),[isabelle.Const("k"),isabelle.Const("l")])])
    res.append(isabelle.isabelleLemma(assms=[cond3,cond31,cond4,cond5], \

            conclusion=isabelle.Op("&",dpred1,dpred2),name="DSafeAndderiveAll", \
            proof=[isabelle.autoProof(unfolds=unfolds,usings=usings)]))


    '''lemma rulesIsSym:
    "symProtRules' N (rules N)"
    using symProtAll rules_def symProtRulesUnion by presburger'''
    name="rulesIsSym"
    pred=isabelle.Fun(isabelle.Const("symProtRules'"),[isabelle.Const("N"), \
        isabelle.Fun(isabelle.Const("rules"),[isabelle.Const("N")])])
    proof=[isabelle.IsabelleApplyRuleProof(name="symProtRulesUnion, blast intro:symProtAll",unfolds=["rules"],plus="+"),
    isabelle.blastProof(unfolds=["rules"],intros=["symProtAll"],introITag="intro:")]
    #res.append(isabelle.isabelleLemma(assms=[],name=name,conclusion=pred,proof=proof))

    name="rule_refsIsSym"
    pred=isabelle.Fun(isabelle.Const("symProtRules'"),[isabelle.Const("N"), \
        isabelle.Fun(isabelle.Const("rule_refs"),[isabelle.Const("D"),isabelle.Const("N")])])
    #proof=isabelle.presburgerProof(usings=["symProtAllRef", "rule_refs_def", "symProtRulesUnion"])
    proof=[isabelle.IsabelleApplyRuleProof(name="symProtRulesUnion, blast intro:symProtAllRef",unfolds=["rule_refs"],plus="+"),
    isabelle.blastProof(unfolds=["rule_refs"],intros=["symProtAllRef"],introITag="intro:")]
    res.append(isabelle.isabelleLemma(assms=[],name=name,conclusion=pred,proof=proof))

    name="DABSrulesIsSym"
    pred=isabelle.Fun(isabelle.Const("DsymProtRules'"),[isabelle.Const("D"), \
        isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("N")])])
     
    proof=[isabelle.IsabelleApplyRuleProof(name="DsymProtRulesUnion, blast intro:DsymProtAllRef",unfolds=["ABS_rules"],plus="+"),
    isabelle.blastProof(intros=["DsymProtAllRef"],introITag="intro:")]
    res.append(isabelle.isabelleLemma(assms=[],name=name,conclusion=pred,proof=proof))
    
    '''lemma rules2WellTyped:
    "r \<in> rules2 N \<Longrightarrow> deriveRule (env N) r"
    unfolding rules2_def'''
    name="rules2WellTyped"
    assm=isabelle.Op(":",isabelle.Const("r"),isabelle.Fun(isabelle.Const("rule_refs"),[isabelle.Const("D"),isabelle.Const("N")]))
    pred=isabelle.Fun(isabelle.Const("deriveRule"),[ \
        isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]), isabelle.Const("r")])
    proof=isabelle.autoProof(unfolds=["rule_refs"],usings=["deriveAllRef"])
    res.append(isabelle.isabelleLemma(name="rule_refsWellTyped",assms=[assm],conclusion=pred,proof=[proof]))

    #generate the lemma invOnStateOfN1:
    '''"reachableUpTo (allInitSpecs N) (rule_refs N) k s ⟹
    fitEnv s (env N)"'''
    name="ReachStafitEnv"
    assm=isabelle.Fun(isabelle.Const("reachableUpTo"), [(isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("N")])), \
         isabelle.Fun(isabelle.Const("rule_refs"), [isabelle.Const("D"),isabelle.Const("N")]), isabelle.Const("k"), isabelle.Const("s")] )
    conclusion=isabelle.Fun(isabelle.Const("fitEnv"), \
        [isabelle.Const("s"), isabelle.Fun(isabelle.Const("env"), [isabelle.Const("N")])])
    '''proof1=isabelle.IsabelleApplyRuleProof(name="invIntro", \
        rule_tac="?fs=\" (allInitSpecs N)\"  and rs=\"(rule_refs N)\" and k=\"k\"")'''
    proof1=isabelle.IsabelleApplyEruleProof(name="invIntro1")
    #proof2=isabelle.subgoalProof(fors=["s0"])
    proof21= isabelle.IsabelleApplyRuleProof(unfolds=["fitEnv"],name="allI")
    proof22=isabelle.IsabelleApplyRuleProof(name="impI")
    proof23=isabelle.casetacProof(goal=isabelle.Const("v"))
    #proof24=isabelle.subgoalProof
    initSpecsOnGlobal=list(filter(lambda x:x.isGlobal,initSpecs))
    '''print("initSpecsOnGlobal[0]=")
    print(str(initSpecsOnGlobal[0]))'''
    initSpecsOnParam=list(filter(lambda x: not(x.isGlobal),initSpecs))
    
    '''print("initSpecsOnparam[0]=")'''
    '''print(str(initSpecsOnParam[0]))'''
    proofs5=[]
    for spec in initSpecsOnGlobal:
        pred=isabelle.Op("=",isabelle.Const("x1"),isabelle.Const("''"+spec.assignVar+"''"))
        proofs5.append(isabelle.casetacProof(pred))
        proofs5.append(spec.genInitSubgoalProof())
        proofs5.append(isabelle.autoProof(goalNum="1"))
        proofs5.append(isabelle.autoProof(goalNum="1"))
    proof25=isabelle.subgoalProof(fors= ["v" ,"x1"],proofs=proofs5+[isabelle.autoProof()])
    proofs6=[]
    for spec in initSpecsOnParam:
        pred=isabelle.Op("=",isabelle.Const("x21"),isabelle.Const("''"+spec.assignVar+"''"))
        proofs6.append(isabelle.casetacProof(pred))
        proofs6.append(spec.genInitSubgoalProof())
        proofs6.append(isabelle.autoProof(goalNum="1"))
        proofs6.append(isabelle.autoProof(goalNum="1"))
    proof26=isabelle.subgoalProof(fors= ["v" ,"x21","x22"],proofs=proofs6+[isabelle.autoProof()])
    proof2=isabelle.subgoalProof(fors=["s0"],proofs=[proof21,proof22,proof23,proof25,proof26]+[isabelle.autoProof()])
    autoIntros=["Un_iff"]+["lemma"+k+"_fitEnv" for k in prot.ori_rule_map.keys()]
    proof3=isabelle.subgoalProof(fors=["r","sk"],proofs=[isabelle.autoProof(unfolds=["rule_refs"],introITag="intro",intros=autoIntros)])
    '''proof7=isabelle.subgoalProof(fors=[],proofs=[isabelle.autoProof()])
    proof8s=[isabelle.autoProof(unfolds=["rule_refs"])] + \
        [isabelle.autoProof(unfolds=[n+"_refs",n+"_ref"]) for n in prot.ori_rule_map.keys()]
    proof8=isabelle.subgoalProof(fors=[],proofs=proof8s)
    proof9=isabelle.autoProof()'''
    lemma=isabelle.isabelleLemma(assms=[assm],conclusion=conclusion,name=name,proof=[proof1,proof2,proof3])
    #generate the main lemma apply(rule_tac ?fs=" (allInitSpecs N)"  and rs="(rule_refs N)" and k="k" in invIntro)
    res.append(lemma)

    name="absProtSim1"
    assm1=isabelle.Op("<",isabelle.Const("0"),isabelle.Const("N"))
    assm2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
    '''assm31=isabelle.Op("<=",isabelle.Const("l"),isabelle.Const("1"))    
    assm32=isabelle.Op(":",isabelle.Const("invL"),isabelle.Fun(isabelle.Const("set"),[isabelle.Fun(isabelle.Const("InvS'"),[isabelle.Const("N")])]))
    assm33=isabelle.Op(":",isabelle.Const("f"),isabelle.Fun(isabelle.Const("set"),[isabelle.Const("InvL")]))
    assm34=isabelle.Fun(isabelle.Const("reachableUpTo"),[])
    assm5=isabelle.Fun(isabelle.Const("formEval"), \
    [isabelle.Fun(isabelle.Const("absTransfForm"),[isabelle.Fun(isabelle.Const("env"), [isabelle.Const("N")]), isabelle.Const("M"), \
        isabelle.Fun(isabelle.Const("f"),[isabelle.Const( "0"),isabelle.Const( "l")])])])
    assm3=isabelle.Quant("\<forall>", "i", isabelle.Quant("\<forall>", "invL", isabelle.Quant("\<forall>", "f", isabelle.Quant("\<forall>", "s",isabelle.Quant("\<forall>", "l" , \
        isabelle.Op("-->",isabelle.Op("&",isabelle.Op("&",isabelle.Op("&",assm31,assm32),assm33),assm34),assm5))))))'''
    assm3=isabelle.Fun(isabelle.Const("isProtObsInvSet"),[isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("M")]), \
        isabelle.Op("`",isabelle.Fun(isabelle.Const("absTransfForm"),[isabelle.Fun(isabelle.Const("env"),[isabelle.Const("N")]),isabelle.Const("M")]), \
            isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("N")])), \
        isabelle.Fun(isabelle.Const("set"),[isabelle.Fun(isabelle.Const("InvS'"),[isabelle.Const("N")])]), isabelle.Const("M"), \
        isabelle.Fun(isabelle.Const("env"), [isabelle.Const("N")])    ])
    conclusion=isabelle.Fun(isabelle.Const("isParamProtInvSet"),[isabelle.Fun(isabelle.Const("rules"),[isabelle.Const("D"),isabelle.Const("N")]), \
        isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("N")]), \
        isabelle.Fun(isabelle.Const("set"),[isabelle.Fun(isabelle.Const("InvS"),[isabelle.Const("N")])]), isabelle.Const("N")    ])
    proof0=isabelle.IsabelleApplyRuleProof(name="allI",unfolds=["isParamProtInvSet"])
    proof1= isabelle.IsabelleApplyRuleProof(name="CMP", \
        rule_tac="?rs2.0 = \"rule_refs D N\" and env=\"env N\" and S=\"set (InvS N)\" and S'=\"set (InvS' N)\" and M=M and absRules=\"ABS_rules D M\"")
    proof2=isabelle.subgoalProof(fors=["r"],proofs=[isabelle.autoProof(usings=["wellFormedRule_refs"])])
    #revised at 2024/4/26
    proof3=isabelle.subgoalProof(proofs=[isabelle.autoProof(unfolds=["InvS'"]+nameOflemmasFors1,usings=["symInvs"])]) if \
    len(lemmasForsymInvsLemma)!=0 else isabelle.subgoalProof(proofs=[isabelle.autoProof(unfolds=["InvS'"]+nameOflemmasFors1)])
    proof4=isabelle.subgoalProof(proofs=[isabelle.autoProof()])
    proof5=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["symPreds"])])
    
    proof6=isabelle.subgoalProof(proofs=[isabelle.autoProof()])
    
    proof7=isabelle.subgoalProof(proofs=[isabelle.autoProof()])
    proof8=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["SafeAndderiveAll"])])
    proof9=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["StrengthRelRules2Rule_refs"])])
    proof10=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["rule_refsIsSym"])])
    #(*proof11=isabelle.subgoalProof(proofs=[isabelle.autoProof()])*)
    proof12=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["rule_refsWellTyped"])])
    proof13=isabelle.subgoalProof(proofs=[isabelle.autoProof()])
    proof14=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["ReachStafitEnv"])])
    usingLemmaN1=["absTransf"+n for n in nameOfLemmas1]
    '''proof15=isabelle.subgoalProof(proofs=[isabelle.autoProof(unfolds=["InvS'"]+nameOflemmasFors1, \
        usings=usingLemmaN1)])'''
    proof161=isabelle.autoProof(unfolds=["InvS","InvS'"])
    proof162s=[]
    for n in lemmasFor_List:
        thisUsing="strengthenVsObsLs_"+n
        proof162s.append(isabelle.subgoalProof(fors=[],proofs=[isabelle.autoProof(usings=[thisUsing])]))

    usingLemmaN1=["strengthenVsObsLs_"+n for n in lemmasFor_List]
    proof16=isabelle.subgoalProof(proofs=[proof161]+proof162s)   
    proof17s=[isabelle.IsabelleApplyRuleProof(name="equivRuleSetReflex"), \
        isabelle.autoProof(usings=["ABS_all "])]
    '''
     apply (rule equivRuleSetReflex)
    using ABS_all 
    subgoal
    unfolding InvS_def InvS'_def
    using strengthenVsObsLs_lemmasFor_Idle by auto'''

   
    '''unfolding InvS_def lemmasFor_Idle_def  
    using symInvs by auto
  subgoal
    using rulesIsSym by auto
  subgoal StrengthRelRules2Rule_refs
    using symPreds by auto
  subgoal 
    using assms(2) by auto
  subgoal
    using assms(3) by auto'''
    res.append(isabelle.isabelleLemma(name="absProtSim",assms=[assm1,assm2,assm3],conclusion=conclusion,
    proof=[proof1,proof2,proof3,proof4,proof5,proof6,proof7,proof8,proof9,proof10,proof12,proof13, \
        proof14,proof16]+proof17s))
    
    name="dabsAbsProtImpAbsProt1"
    assm1=isabelle.Op("<",isabelle.Const("0"),isabelle.Const("D"))
    assm2=isabelle.Op("=",isabelle.Const("M"),isabelle.Const("1"))
    '''a2:"isParamProtInvSet  (ABS_rules 1 M) ( DabsInitSpec M) (set (InvS' N)) M " 

    and a3: "isDParamProtInv (ABS_rules 1 M) ( DabsInitSpec M) Lemma_2'  0 M" '''
    assm3=isabelle.Fun(isabelle.Const("isDParamProtInv"),[isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("1"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("DabsInitSpec"),[isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("set"),[isabelle.Fun(isabelle.Const("InvS'"),[isabelle.Const("N")])]), 
        isabelle.Const("M")    ])
    assm4=isabelle.Fun(isabelle.Const("isParamProtInvSet"),[isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("1"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("DabsInitSpec"),[isabelle.Const("M")]), \
        isabelle.Const("Lemma_2'"),\
        isabelle.Const("0"),isabelle.Const("M")    ])
    '''shows "isParamProtInvSet  (ABS_rules D M) (allInitSpecs D M) (set (InvS' N)) M ∧
       isDParamProtInv  (ABS_rules D M) (allInitSpecs D M) Lemma_2 D M"'''
    conclusion1=isabelle.Fun(isabelle.Const("isParamProtInvSet"),[isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("set"),[isabelle.Fun(isabelle.Const("InvS"),[isabelle.Const("N")])]), isabelle.Const("M")    ])
    conclusion2=isabelle.Fun(isabelle.Const("isDParamProtInv"),[isabelle.Fun(isabelle.Const("ABS_rules"),[isabelle.Const("D"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("allInitSpecs"),[isabelle.Const("D"),isabelle.Const("M")]), \
        isabelle.Fun(isabelle.Const("Lemma_2"),[isabelle.Const("N")]), \
        isabelle.Const("D"), isabelle.Const("M")   ])
    conclusion=isabelle.Op("&",conclusion1,conclusion2)
    '''apply(rule_tac   rs="(ABS_rules D M)" and ?DabsRules ="ABS_rules 1 M" and 
      Is="allInitSpecs D M" and dataInv'="Lemma_2'" and env="env M" and gv="   (''auxData'')"
      and pv="    (''n.data'') "  and D="D" and M="M"   in DABS1)'''
    proof1= isabelle.IsabelleApplyRuleProof(name="DABS1", \
        rule_tac="?rs = \"ABS_rules D M\" and DabsRules=\"ABS_rules 1 M\" and Is=\"allInitSpecs D M\" and dataInv'=\"Lemma_2'\" and env=\"env M'\" and gv=\"''auxData''\" and pv=\"''n.data''\"  and D=\"D\" and M=\"M\"")
    
    ''' subgoal 
    by auto
  subgoal
    by (auto intro:DwellFormedABS_rules)
  subgoal
    apply(subgoal_tac "( DabsInitSpec M)= (DabsTransfForm (env M) ` allInitSpecs D M )")
    using a2    apply ( simp  del:allInitSpecs_def DabsTransfForm.simps ) 
    apply(rule sym) using DabsSpec a4  apply(unfold DabsInitSpec_def)
     by presburger
   
  subgoal
    apply(subgoal_tac "( DabsInitSpec M)= (DabsTransfForm (env M) ` allInitSpecs D M )")
     using a3    apply ( simp  del:allInitSpecs_def DabsTransfForm.simps ) 
    apply(rule sym) using DabsSpec a4  apply(unfold DabsInitSpec_def)
      by presburger
  subgoal
    unfolding Lemma_2'_def using a4  a6 by auto   
  subgoal thm DsafeAndderiveAll 
     using DsafeAndderiveAll a4   a6
     by auto
   subgoal
     by (simp add: DsymLemma_2)
   subgoal
     by blast
   subgoal
     apply(unfold dataParamVsObs_def  Lemma_2_def  Lemma_2'_def)
     apply(rule_tac x="λi. IVar (Para ''n'' i) =⇩f Const E" in exI)
     
     by auto
   subgoal
     by(auto intro: ReachABSKeepData)
   subgoal
     using DABSrulesIsSym by blast 
   subgoal thm ABS_RulesWellTyped
     by (simp add: ABS_RulesWellTyped) 
   subgoal
     using a4   by auto
   subgoal
     by (simp add: ReachABSStafitEnv)
   subgoal
     using a4 by arith
   subgoal
     using DABS_all ‹1 ≤ D› a6 by blast'''
    proof2=isabelle.subgoalProof(proofs=[isabelle.autoProof()])
    #revised at 2024/4/26
    proof3=isabelle.subgoalProof(proofs=[isabelle.autoProof(introITag="intro",intros=["DwellFormedABS_rules"])]) 
    proof4=isabelle.subgoalProof(proofs=[isabelle.metisProof(intros=["lemmaDabsInitSpec", "a2"])])
    proof5=isabelle.subgoalProof(proofs=[isabelle.autoProof(intros=["lemmaDabsInitSpec", "a3"])])
    
    proof6=isabelle.subgoalProof(proofs=[isabelle.autoProof(unfolds=["Lemma_2'"],usings=["a4","a6"] )])
    
    proof7=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["DsafeAndderiveAll", "a4","a6"])])
    proof8=isabelle.subgoalProof(proofs=[isabelle.autoProof(simpadds=["DsymLemma_2"])])
    proof9=isabelle.subgoalProof(proofs=[isabelle.blastProofProof()])
    proof10=isabelle.subgoalProof(proofs=[isabelle.IsabelleApplyRuleProof(name="exI", \
        rule_tac="x = %s"%("aaa"),unfolds=["dataParamVsObs",  "Lemma_2'",  "Lemma_2"]),\
        isabelle.autoProof()])
    #(*proof11=isabelle.subgoalProof(proofs=[isabelle.autoProof()])*)
    proof12=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["rule_refsWellTyped"])])
    proof13=isabelle.subgoalProof(proofs=[isabelle.autoProof()])
    proof14=isabelle.subgoalProof(proofs=[isabelle.autoProof(usings=["ReachStafitEnv"])])
    usingLemmaN1=["absTransf"+n for n in nameOfLemmas1]
    '''proof15=isabelle.subgoalProof(proofs=[isabelle.autoProof(unfolds=["InvS'"]+nameOflemmasFors1, \
        usings=usingLemmaN1)])'''
    proof161=isabelle.autoProof(unfolds=["InvS","InvS'"])
    proof162s=[]
    for n in lemmasFor_List:
        thisUsing="strengthenVsObsLs_"+n
        proof162s.append(isabelle.subgoalProof(fors=[],proofs=[isabelle.autoProof(usings=[thisUsing])]))

    usingLemmaN1=["strengthenVsObsLs_"+n for n in lemmasFor_List]
    proof16=isabelle.subgoalProof(proofs=[proof161]+proof162s)   
    proof17s=[isabelle.IsabelleApplyRuleProof(name="equivRuleSetReflex"), \
        isabelle.autoProof(usings=["ABS_all "])]
    '''
     apply (rule equivRuleSetReflex)
    using ABS_all 
    subgoal
    unfolding InvS_def InvS'_def
    using strengthenVsObsLs_lemmasFor_Idle by auto'''

   
    '''unfolding InvS_def lemmasFor_Idle_def  
    using symInvs by auto
  subgoal
    using rulesIsSym by auto
  subgoal StrengthRelRules2Rule_refs
    using symPreds by auto
  subgoal 
    using assms(2) by auto
  subgoal
    using assms(3) by auto'''
    res.append(isabelle.isabelleLemma(name="absProtSim",assms=[assm1,assm2,assm3],conclusion=conclusion,
    proof=[proof1,proof2,proof3,proof4,proof5,proof6,proof7,proof8,proof9,proof10,proof12,proof13, \
        proof14,proof16]+proof17s))
    res.append(isabelle.isabelleLemma(name="dabsAbsProtImpAbsProt1",assms=[assm1,assm2,assm3],conclusion=conclusion,
    proof=[proof1,proof2,proof3,proof4,proof5,proof6,proof7,proof8,proof9,proof10,proof12,proof13, \
        proof14,proof16]+proof17s))
    return(res)   

#light-weight scale 
def translateOrigProtSpecs(prot):
    res = []
    rulesDefList=[]
    deriveAllLLemmaist=[]
    symProtAllLemmaList=[]
    dsymProtAllLemmaList=[]
    deriveAllLLemmaProofUnfolds1=[]
    symProtAllLemmaProofUsings2=[]
    
    for decl in prot.decls:
        
        
        if isinstance(decl, murphi.MurphiRule):
            declcp=copy.deepcopy(decl)
            declcp.name="orig"+declcp.name
            res.append(translateRule(declcp))
            if True: #(decl in prot.ori_rule_map.values()):
                if (decl in prot.abs_rule_map.values()):
                    res.append(genRuleDSymLemma(decl))
                else:
                    res.append(genRuleSymLemma(decl))
                #if (decl not in prot.abs_rule_map.values()):
                #    res.append(genRuleDSymLemma(decl))
                    #pass #res.append(genRuleSymLemma(decl))
                def1,lemma1,lemma2,term1,unfolds,usings=translateRule1(declcp)
                res.append(def1)
                deriveAllLLemmaist.append(lemma1)
                if (decl in prot.ori_rule_map.values()):
                    symProtAllLemmaList.append(lemma2)
                    dsymProtAllLemmaList.append(dlemma2)
                    rulesDefList.append(term1)
                deriveAllLLemmaProofUnfolds1.extend(unfolds)
                if (decl in prot.ori_rule_map.values()):
                    symProtAllLemmaProofUsings2.extend(usings)


        elif isinstance(decl, murphi.MurphiRuleSet):
            declcp=copy.deepcopy(decl)
            declcp.rule.name="orig"+declcp.rule.name if isinstance(decl.rule,murphi.MurphiRule) else\
            declcp.rule.name
            res.append(translateRuleSet(declcp))
            if True: #(decl in prot.ori_rule_map.values()):
                if (decl not in prot.abs_rule_map.values()):
                    pass#res.append(genRuleSetSymLemma(decl))
                def1,lemma1,lemma2,dlemma2,term1,unfolds,usings=translateRuleSets(declcp)
                #rulesDefList.append(term1)
                res.append(def1)
                #if (decl in prot.ori_rule_map.values()):
                deriveAllLLemmaist.append(lemma1)
                if (decl in prot.ori_rule_map.values()):    
                    symProtAllLemmaList.append(lemma2)
                    dsymProtAllLemmaList.append(dlemma2)
                    rulesDefList.append(term1)
                deriveAllLLemmaProofUnfolds1.extend(unfolds)
                if (decl in prot.ori_rule_map.values()):
                    symProtAllLemmaProofUsings2.extend(usings)

        elif isinstance(decl, murphi.MurphiInvariant):
            pass
            #res.append(translateInvariant(decl))
    typ = isabelle.FunType(isabelle.nat, isabelle.FunType(isabelle.nat, isabelle.setType(isabelle.rule)))
    def_rules=isabelle.Definition(name="rules",typ=typ,val=isabelle.UN(rulesDefList),args=["D","N"])
    res.append(def_rules)
    return res

def translateProtocol(prot, str_data):
    defs = []
    defs.extend(translateAllEnum(prot, str_data))
    defs.extend(translateBooleans())
    defs.extend(translateEnvByStartState(prot))
    (res,initSpecs)=translateStartState(prot)
    defs.extend(res)
    str_data = str_data[1:]
    defs.extend(translateAllSpecs(prot)) 
    defs.extend(genSymLemmas(prot))
    defs.extend(genSterengthenLemmas(prot,str_data))
    defs.extend(genAllInvariantsPrime(prot))
    defs.extend(genAllRuleSetStuff(prot,str_data,initSpecs))
    return defs

def translateFile(filename, str_file, theory_name):
    origProtName = filename.replace("ABS_rep_","",1)
    print(origProtName)
    origProt = murphiparser.parse_file(origProtName)
    origProt.addition()    
    orig_defs=translateOrigProtSpecs(origProt )

    prot = murphiparser.parse_file(filename)
    prot.addition()

    with open(str_file, "r") as spec1:
        str_data = json.load(spec1)

    with open(theory_name + ".thy", "w") as f:
        f.write(isabelle.header(theory_name))
        defs = translateProtocol(prot, str_data)
        for t in defs:#defs: #orig_defs.extend(defs):
            # try:
            #     print("t=%s\n"%str(t))
            # except(AttributeError):
            #     print(type(t))
            #     print("t=%s\n"%str(t.name))    
            f.write(t.export() + '\n')
        f.write("(*----------------------------*)\n")
        for t in  orig_defs:#defs: #orig_defs.extend(defs):
            # try:
            #     print("t=%s\n"%str(t))
            # except(AttributeError):
            #     print(type(t))
            #     print("t=%s\n"%str(t.name))    
            f.write(t.export() + '\n')
        f.write("end\n")


    # print ("Number of rule is%d"%len(prot.ori_rule_map.items()))
    '''for k,val in prot.lemma_map.items():
        extLemma=extMurphiInvariant(val)
        extLemma.test()
        print((extLemma.genLemma1().export()))'''
if __name__ == "__main__":
    translateFile("mutualEx1.m", "mutualEx1.json", "mutualEx_str.json", "MutualEx")
    translateFile("german.m", "german.json","german_str.json", "German")
    translateFile("flash_ctc10.m", "flash_ctc10.json", "flash_str.json", "Flash")
    translateFile("mesi.m", "mesi.json", "mesi_str.json", "Mesi")
    