// L5-typecheck
// ========================================================
import { equals, filter, flatten, includes, map, intersection, zipWith, reduce, is } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, unparse, parseL51,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp, SetExp, LitExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isSetExp, isLitExp, 
         isDefineTypeExp, isTypeCaseExp, DefineTypeExp, TypeCaseExp, CaseExp, makeLitExp, makeStrExp, expComponents, isVarDecl } from "./L5-ast";
import { applyTEnv, isEmptyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
         parseTE, unparseTExp, Record,
         BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, UserDefinedTExp, isUserDefinedTExp, UDTExp, 
         isNumTExp, isBoolTExp, isStrTExp, isVoidTExp,
         isRecord, ProcTExp, makeUserDefinedNameTExp, Field, makeAnyTExp, isAnyTExp, isUserDefinedNameTExp, makeUserDefinedTExp, isEmptyTVar, isTVar, tvarContents, isEmptyTupleTExp, isNonEmptyTupleTExp, NonEmptyTupleTExp, UserDefinedNameTExp, makeTVar, makeRecord } from "./TExp";
import { isEmpty, allT, first, rest, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, mapv, mapResult, isFailure, either, isOk } from '../shared/result';
import { isCompoundSExp, valueToString, isClosure, makeSymbolSExp, isSymbolSExp } from './L5-value';

// L51
export const getTypeDefinitions = (p: Program): UserDefinedTExp[] => {
    const iter = (head: Exp, tail: Exp[]): UserDefinedTExp[] =>
        isEmpty(tail) && isDefineTypeExp(head) ? [head.udType] :
        isEmpty(tail) ? [] :
        isDefineTypeExp(head) ? cons(head.udType, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getDefinitions = (p: Program): DefineExp[] => {
    const iter = (head: Exp, tail: Exp[]): DefineExp[] =>
        isEmpty(tail) && isDefineExp(head) ? [head] :
        isEmpty(tail) ? [] :
        isDefineExp(head) ? cons(head, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getRecords = (p: Program): Record[] =>
    flatten(map((ud: UserDefinedTExp) => ud.records, getTypeDefinitions(p)));

// L51
export const getItemByName = <T extends {typeName: string}>(typeName: string, items: T[]): Result<T> =>
    isEmpty(items) ? makeFailure(`${typeName} not found`) :
    first(items).typeName === typeName ? makeOk(first(items)) :
    getItemByName(typeName, rest(items));

// L51
export const getUserDefinedTypeByName = (typeName: string, p: Program): Result<UserDefinedTExp> =>
    getItemByName(typeName, getTypeDefinitions(p));

// L51
export const getRecordByName = (typeName: string, p: Program): Result<Record> =>
    getItemByName(typeName, getRecords(p));

// L51
// Given the name of record, return the list of UD Types that contain this record as a case.
export const getRecordParents = (typeName: string, p: Program): UserDefinedTExp[] =>
    filter((ud: UserDefinedTExp): boolean => map((rec: Record) => rec.typeName, ud.records).includes(typeName),
        getTypeDefinitions(p));


// L51
// Given a user defined type name, return the Record or UD Type which it names.
// (Note: TS fails to type check either in this case)
export const getTypeByName = (typeName: string, p: Program): Result<UDTExp> => {
    const ud = getUserDefinedTypeByName(typeName, p);
    if (isFailure(ud)) {
        return getRecordByName(typeName, p);
    } else {
        return ud;
    }
}

// TODO L51 - VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
// Is te1 a subtype of te2?
const isSubType = (te1: TExp, te2: TExp, p: Program): boolean =>{
    if(isAnyTExp(te2)) return true;
    const validateProcTExp = (texp1: ProcTExp, texp2: TExp): boolean => {
        if(isProcTExp(texp2)){
            if(!(isSubType(texp1.returnTE, texp2.returnTE, p))) return false;
            const t1Params = texp1.paramTEs;
            const t2Params = texp2.paramTEs;
            for (let i = 0; i < t1Params.length; i++) {
                if(!(isSubType(t1Params[i], t2Params[i], p))) return false;
            }

        } else return false;

        return true;
    }

    const validateNETupleTExp = (texp1: NonEmptyTupleTExp, texp2: TExp): boolean => {
        if(isNonEmptyTupleTExp(texp2)){
            const t1Tes = texp1.TEs;
            const t2Tes = texp2.TEs;
            for (let i = 0; i < t1Tes.length; i++) {
                if(!(isSubType(t1Tes[i], t2Tes[i], p))) return false;
            }

        }else return false;

        return true;
    }

    const validateRecordTExp = (texp1: Record, texp2: TExp): boolean => {
        if(isUserDefinedTExp(texp2)) return getRecordParents(texp1.typeName, p).includes(texp2);
        if(isUserDefinedNameTExp(texp2)) {
            const res = getUserDefinedTypeByName(texp2.typeName, p);
            if(isOk(res)) return getRecordParents(texp1.typeName, p).includes(res.value);
            else return false;
        }
        return false;
    }

    const validateUserDefinedTExp = (texp1: UserDefinedTExp, texp2: TExp): boolean => {
        if(isUserDefinedTExp(texp2)) return getRecordParents(texp1.typeName, p).includes(texp2);
        if(isUserDefinedNameTExp(texp2)) {
            const res = getUserDefinedTypeByName(texp2.typeName, p);
            if(isOk(res)) return getRecordParents(texp1.typeName, p).includes(res.value);
            else return false;
        }
        return false;
    }
    
    const up = (x?: TExp): Result<string> =>
        isNumTExp(x) ? makeOk('number') :
        isBoolTExp(x) ? makeOk('boolean') :
        isStrTExp(x) ? makeOk('string') :
        isVoidTExp(x) ? makeOk('void') :
        isAnyTExp(x) ? makeOk('any') :
        isEmptyTVar(x) ? makeOk(x.var) :
        isUserDefinedNameTExp(x) ? makeOk(x.typeName) :
        isTVar(x) ? up(tvarContents(x)) :
        isUserDefinedTExp(x) ? makeOk(x.typeName) :
        isRecord(x) ? makeOk(x.typeName) :
        isProcTExp(x) ? makeOk("ProcExp") :
        isEmptyTupleTExp(x) ? makeOk("Empty") :
        isNonEmptyTupleTExp(x) ? makeOk("NonEmptyTupleTExp") :
        x === undefined ? makeFailure("Undefined TVar") :
        x;

    const preres1 = up(te1);
    const preres2 = up(te2);

    if(isOk(preres1) && isOk(preres2)){

        if(isProcTExp(te1)) return validateProcTExp(te1, te2);
        if(isNonEmptyTupleTExp(te1)) return validateNETupleTExp(te1, te2);
        
        const res1 = getTypeByName(preres1.value, p);
        const res2 = getTypeByName(preres2.value, p);
        if(isOk(res1) && isOk(res2)){
            if(isRecord(res1.value)) return validateRecordTExp(res1.value, te2);
            if(isUserDefinedNameTExp(res1.value)) return validateUserDefinedTExp(res1.value, te2);
            if(isUserDefinedTExp(res1.value)) return validateUserDefinedTExp(res1.value, te2);
        }
        if(preres1.value == preres2.value) return true;
    }  
// getTypeDefinitions()
// getDefinitions()
// getRecords()
// getItemByName()
// getUserDefinedTypeByName()
// getRecordByName()
// getRecordParents()
// getTypeByName()

    return false;
}


// TODO L51: VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
// Change this definition to account for user defined types
// Purpose: Check that the computed type te1 can be accepted as an instance of te2
// test that te1 is either the same as te2 or more specific
// Deal with case of user defined type names 
// Exp is only passed for documentation purposes.
// p is passed to provide the context of all user defined types
export const checkEqualType = (te1: TExp, te2: TExp, exp: Exp, p: Program): Result<TExp> =>
  equals(te1, te2) ? makeOk(te2) : isSubType(te1, te2, p) ? makeOk(te2) : makeFailure("Not equal");


// L51
// Return te and its parents in type hierarchy to compute type cover
// Return type names (not their definition)
export const getParentsType = (te: TExp, p: Program): TExp[] =>
    (isNumTExp(te) || isBoolTExp(te) || isStrTExp(te) || isVoidTExp(te) || isAnyTExp(te)) ? [te] :
    isProcTExp(te) ? [te] :
    isUserDefinedTExp(te) ? [te] :
    isRecord(te) ? getParentsType(makeUserDefinedNameTExp(te.typeName), p) :
    isUserDefinedNameTExp(te) ?
        either(getUserDefinedTypeByName(te.typeName, p),
                (ud: UserDefinedTExp) => [makeUserDefinedNameTExp(ud.typeName)],
                (_) => either(getRecordByName(te.typeName, p),
                            (rec: Record) => cons(makeUserDefinedNameTExp(rec.typeName), 
                                                  map((ud) => makeUserDefinedNameTExp(ud.typeName), 
                                                      getRecordParents(rec.typeName, p))),
                            (_) => [])) : 
    [];

// L51
// Get the list of types that cover all ts in types.
export const coverTypes = (types: TExp[], p: Program): TExp[] =>  {
    // [[p11, p12], [p21], [p31, p32]] --> types in intersection of all lists
    const parentsList : TExp[][] = map((t) => getParentsType(t,p), types);
    return reduce<TExp[], TExp[]>(intersection, first(parentsList), rest(parentsList));
}

// Return the most specific in a list of TExps
// For example given UD(R1, R2):
// - mostSpecificType([R1, R2, UD]) = R1 (choses first out of record level)
// - mostSpecificType([R1, number]) = number  
export const mostSpecificType = (types: TExp[], p: Program): TExp =>
    reduce((min: TExp, element: TExp) => isSubType(element, min, p) ? element : min, 
            makeAnyTExp(),
            types);

// L51
// Check that all t in types can be covered by a single parent type (not by 'any')
// Return most specific parent
export const checkCoverType = (types: TExp[], p: Program): Result<TExp> => {
    const cover = coverTypes(types, p);
    return isEmpty(cover) ? makeFailure(`No type found to cover ${map((t) => JSON.stringify(unparseTExp(t), null, 2), types).join(" ")}`) :
    makeOk(mostSpecificType(cover, p));
}


// Compute the initial TEnv given user defined types
// =================================================
// TODO L51
// Construct type environment for the user-defined type induced functions
// Type constructor for all records
// Type predicate for all records
// Type predicate for all user-defined-types
// All globally defined variables (with define)

// TODO: Define here auxiliary functions for TEnv computation

// TOODO L51 - VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
// Initialize TEnv with:
// * Type of global variables (define expressions at top level of p)
// * Type of implicitly defined procedures for user defined types (define-type expressions in p)
export const initTEnv = (p: Program): TEnv =>{
    const typeDefs = getTypeDefinitions(p);
    const vars : string[] = [];
    const texps : TExp[] = [];

    typeDefs.forEach((currTDef) => {
        const predicate = currTDef.typeName.concat("?");
        const res = getUserDefinedTypeByName(currTDef.typeName, p);
        if(isFailure(res)) return false;

        //const currTExp = isOk(res) ? res.value : makeUserDefinedTExp("" , []);

        vars.push(predicate);
        texps.push(makeProcTExp([makeAnyTExp()], makeBoolTExp()));

    });

    const records = getRecords(p);
    records.forEach((currRec) => {
        const constructorName = "make-".concat(currRec.typeName);
        const predicate = currRec.typeName.concat("?");
        
        const res = getTypeByName(currRec.typeName, p);
        if(isFailure(res)) return false;

        const currTExp = isOk(res) ? res.value : makeUserDefinedTExp("" , []);

        vars.push(constructorName);
        const fieldsTypes = currRec.fields.reduce((types : TExp[], currField) => {types.push(currField.te); return types;}, [])
        texps.push(makeProcTExp(fieldsTypes, currTExp));

        vars.push(predicate);
        texps.push(makeProcTExp([makeAnyTExp()], makeBoolTExp()));

    })

    const defs = getDefinitions(p);
    defs.forEach((currDef) => {
        vars.push(currDef.var.var);
        texps.push(currDef.var.texp);

    })

    const addProcsArgs = (exp : Exp) : void =>{
        if(isVarRef(exp)) {
            if(!vars.includes(exp.var)){
                vars.push(exp.var);
                texps.push(makeNumTExp());
            }
        }
        expComponents(exp).forEach((comp) => addProcsArgs(comp));
    }

    p.exps.forEach((exp) => addProcsArgs(exp));

    if(vars.length == 0) return makeEmptyTEnv();
    return makeExtendTEnv(vars, texps, makeEmptyTEnv());
}


// Verify that user defined types and type-case expressions are semantically correct
// =================================================================================
// TODO L51
const checkUserDefinedTypes = (p: Program): Result<true> =>{

    const udtTypesExps = getTypeDefinitions(p);
    udtTypesExps.forEach((currUD) => {
        const records = currUD.records;
        records.forEach((currRec) => {
            const parents = getRecordParents(currRec.typeName, p);
            parents.forEach((currParent) => {
                const currParentRecordsNames = currParent.records.reduce((names : string[], currParentRec) => {names.push(currParentRec.typeName); return names;}, []);
                const index = currParentRecordsNames.indexOf(currRec.typeName);
                if(index == -1) return makeFailure("record not in its parent");
                if(isFailure(checkEqualType(currParent.records[index], currRec, makeStrExp(""), p))) return makeFailure("record's definition differs in its parents");
            });
        });
        
    });

    // If a recursive type has no base case !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    return makeOk(true);
}

// TODO L51
const checkTypeCase = (tc: TypeCaseExp, p: Program): Result<true> => {
    // Check that all type case expressions have exactly one clause for each constituent subtype 
    // (in any order)

    const casesExps = tc.cases;
    const casesTypes : string[] = casesExps.reduce((names : string[], currCase) => {
        names.push(currCase.typeName);
        return names;
    }, [])
    const res = getTypeByName(tc.typeName, p);
    if(isOk(res)){
        const udTexp = res.value;
        if(isUserDefinedTExp(udTexp)){ 
            udTexp.records.forEach((record) => {
                const index = casesTypes.indexOf(record.typeName);
                if((index == -1) || record.fields.length != tc.cases[index].varDecls.length) return makeFailure("record not in cases of type-case exp");
            });
        }
    }


    // export interface CaseExp {tag: "CaseExp", typeName: string, varDecls: VarDecl[], body: CExp[]};



    // export interface TypeCaseExp {tag: "TypeCaseExp", typeName: string, val: CExp, cases: CaseExp[]};
    // ( type-case <id> <CExp> ( <case-exp> )+  ) / TypeCaseExp(typeName: string, val: CExp, cases: CaseExp[]) #### L51

    return makeOk(true);
}


// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L51typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL51(concreteExp), (p: Program) => {
        if(isFailure(checkUserDefinedTypes(p))) return makeFailure("bad UserDefinedType");
        return bind(typeofExp(p, initTEnv(p), p), unparseTExp)
    });

// For tests on a single expression - wrap the expression in a program
export const L51typeof = (concreteExp: string): Result<string> =>
    L51typeofProgram(`(L51 ${concreteExp})`);

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv, p: Program): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv, p) :
    isProcExp(exp) ? typeofProc(exp, tenv, p) :
    isAppExp(exp) ? typeofApp(exp, tenv, p) :
    isLetExp(exp) ? typeofLet(exp, tenv, p) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv, p) :
    isDefineExp(exp) ? typeofDefine(exp, tenv, p) :
    isProgram(exp) ? typeofProgram(exp, tenv, p) :
    isSetExp(exp) ? typeofSet(exp, tenv, p) :
    isLitExp(exp) ? typeofLit(exp, tenv, p) :
    isDefineTypeExp(exp) ? typeofDefineType(exp, tenv, p) :
    isTypeCaseExp(exp) ? typeofTypeCase(exp, tenv, p) :
    makeFailure(`Unknown type: ${JSON.stringify(exp, null, 2)}`);


// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: Exp[], tenv: TEnv, p: Program): Result<TExp> =>
    isEmpty(rest(exps)) ? typeofExp(first(exps), tenv, p) :
    bind(typeofExp(first(exps), tenv, p), _ => typeofExps(rest(exps), tenv, p));

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// L51 Todo: cons, car, cdr, list
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51
// Change this definition to account for possibility of subtype expressions between thenTE and altTE
// 
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv, p: Program): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv, p);
    const thenTE = typeofExp(ifExp.then, tenv, p);
    const altTE = typeofExp(ifExp.alt, tenv, p);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp, p));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
                            bind(altTE, (altTE: TExp) =>
                                checkEqualType(thenTE, altTE, ifExp, p)));
    return bind(constraint1, (_c1) => constraint2);
    
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv, p: Program): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv, p), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc, p));
    return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv, p: Program): Result<TExp> =>
    bind(typeofExp(app.rator, tenv, p), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv, p), (typeOfRand: TExp) => 
                                                                checkEqualType(typeOfRand, trand, app, p)),
                                          app.rands, ratorTE.paramTEs);
        return mapv(constraints, _ => ratorTE.returnTE);
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv, p: Program): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv, p), (typeOfVal: TExp) => 
                                                            checkEqualType(varTE, typeOfVal, exp, p)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv), p));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv, p: Program): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${JSON.stringify(exp, null, 2)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI, p), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp, p), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody, p));
};

// TODO - VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
// write the true definition
// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
//   tenv-val = extend-tenv(var:texp; tenv)
// If   type<val>(tenv-val) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv, p: Program): Result<VoidTExp> => {
    const v = exp.var.var;
    const texp = exp.var.texp;
    const val = exp.val;
    const tenvVal = makeExtendTEnv([v], [texp], tenv);
    const constraint = typeofExp(val, tenvVal, p);    
    return mapv(constraint, (_) => makeVoidTExp());
};

// Purpose: compute the type of a program
// Typing rule:
export const typeofProgram = (exp: Program, tenv: TEnv, p: Program): Result<TExp> =>
    typeofExps(exp.exps, tenv, p);

// TODO L51 - **********************************************************************************************************
// Write the typing rule for DefineType expressions
export const typeofDefineType = (exp: DefineTypeExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    const records = exp.udType.records;
    if(records.length == 0) return makeFailure("DefineTypeExp missing records");
    records.forEach((rec) => {
        if(rec.fields.length == 0) return makeFailure("Record in DefineTypeExp missing fields");
    });
    if(isEmptyTEnv(_tenv)) return makeOk(makeUserDefinedNameTExp(exp.typeName));

    const parents = getRecordParents(exp.typeName, _p);
    if((parents.length == 0)) return makeOk(makeUserDefinedNameTExp(exp.typeName));
    else return makeOk(makeUserDefinedNameTExp(parents[0].typeName));


    // const constraint1 = records.reduce((types : Boolean[], rec) => {types.push(rec.tag === "Record"); return types;}, []);
    // if(constraint1.includes(false)) return makeFailure("DefineTypeExp records are bad"); 
    // const constraint2 = records.forEach((rec) => {
    //     if(rec.fields.reduce((fldTypes : Boolean[], currField) => {fldTypes.push(currField.tag === )}, []))

    // })
    //records.reduce((types : Boolean[], rec) => {types.push(rec.tag === "Record"); return types;}, []);
    //const udTypeNames = exp.udType.records.reduce((recTypeNames : string[], currRec : Record) => {recTypeNames.push(currRec.typeName); return recTypeNames;}, [])
    //return parseTExp(exp.typeName, udTypeNames);
}
    

// TODO L51 - VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
export const typeofSet = (exp: SetExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    //const variable = exp.var.var;
    const val = exp.val;
    return typeofExp(val, _tenv, _p);
}
    
// TODO L51 - VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
export const typeofLit = (exp: LitExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    const sexpVal = exp.val;
    if(isCompoundSExp(sexpVal)){
        const firstVal = typeofLit(makeLitExp(sexpVal.val1), _tenv, _p); 
        const secVal = typeofLit(makeLitExp(sexpVal.val2), _tenv, _p); 
        if(isOk(firstVal) && isOk(secVal)) {
            const res = checkEqualType(firstVal.value, secVal.value, exp, _p); // don't know if both types has to beequal????????????????????????
            if(isOk(res)) return res;
        }
        return makeOk(makeAnyTExp());  
     }
     if(isClosure(sexpVal)){
        const argsTEs = map((vd) => vd.texp, sexpVal.params);
        const extTEnv = makeExtendTEnv(map((vd) => vd.var, sexpVal.params), argsTEs, _tenv);
        const retType = typeofExp(sexpVal.body[sexpVal.body.length-1], _tenv, _p);
        if(isOk(retType)){ 
            const constraint1 = bind(typeofExps(sexpVal.body, extTEnv, _p), (body: TExp) => 
                                    checkEqualType(body, retType.value, exp, _p));
            return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));

        }
        return makeFailure("Not Ok in /typecheck/typeofLit()");
     }
    return typeof(sexpVal) === 'string' ? makeOk(makeStrTExp()) : typeof(sexpVal) === 'boolean' ? makeOk(makeBoolTExp()) : typeof(sexpVal) === 'number' ? makeOk(makeNumTExp()) :
    isSymbolSExp(sexpVal) ? makeOk(makeStrTExp()) : isPrimOp(sexpVal) ? typeofPrim(sexpVal) : makeOk(typeofStr(makeStrExp("")));
}

// TODO: L51
// Purpose: compute the type of a type-case
// Typing rule:
// For all user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
//   ( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )
//  TODO
export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {
    // validate each case is a subtype of exp type
    if(isFailure(checkTypeCase(exp, p))) return makeFailure("bad type-case");
    const cases = exp.cases;
    const subTypeVerification = cases.reduce((typesVer : Boolean[], currCase) => {
        typesVer.push(currCase.typeName == exp.typeName || getRecordParents(currCase.typeName, p).reduce((typeNames : string[], currParent) => {
            typeNames.push(currParent.typeName); return typeNames;
        }, []).includes(exp.typeName)); return typesVer;
    }, []);
    if(!subTypeVerification.includes(true)) return makeFailure("Case is not a subtype of a type-case");

    // validate all cases returns same type 
    const firstCase = typeofExps(cases[0].body, tenv, p);
    cases.forEach((currCase) => { 
        if(typeofExps(currCase.body, tenv, p) != firstCase) return makeFailure("Case exp is not of the same type as other cases' exp");
        
        // Validate each case's VarDecl are compatible with its case-type (similar to typeOfProcExp)
        if(isOk(firstCase)){
            const retType = firstCase.value;
            const argsTEs = map((vd) => vd.texp, currCase.varDecls);
            const extTEnv = makeExtendTEnv(map((vd) => vd.var, currCase.varDecls), argsTEs, tenv);
            const constraint1 = bind(typeofExps(currCase.body, extTEnv, p), (body: TExp) => 
                                    checkEqualType(body, retType, exp, p));
            if(isFailure(bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE))))) return makeFailure("case's VarDecl is not compatible with its case-type");
        }
    });

    const out = typeofExps(exp.cases[0].body, tenv, p);
    return out;


    //return makeFailure(`TODO: typecase ${JSON.stringify(exp, null, 2)}`);

}
