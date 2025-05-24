// L5-typecheck.ts
import { equals, is, map, zipWith } from 'ramda';
import {
    isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
    isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, parseL5Exp, unparse,
    AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp,
    Parsed, PrimOp, ProcExp, Program, StrExp,
    parseL5
} from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import {
    isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
    parseTE, unparseTExp,
    BoolTExp, NumTExp, StrTExp, TExp, VoidTExp,
    isTVar,
    TVar,
    makePairTExp,
    isPairTExp
} from "./TExp";
import { isEmpty, allT, first, rest, NonEmptyList, List, isNonEmptyList, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, isOk, isFailure } from '../shared/result';
import { parse as p } from "../shared/parser";
import { format } from '../shared/format';
import { isLitExp, LitExp } from "./L5-ast";
import { SExpValue, isCompoundSExp, isEmptySExp, isSymbolSExp } from "./L5-value";
import { makeTVar } from "./TExp";

/**
 * Checks that two type expressions are equivalent, supporting TVar unification and
 * structural comparison for pairs and procedures.
 * Returns a Result<true> on success, or a Failure with a descriptive message.
 */
const checkEqualType = (te1: TExp, te2: TExp, exp: Exp): Result<true> => {

    // Structural check for pairs
    if (te1.tag === "PairTExp" && te2.tag === "PairTExp") {
        return bind(checkEqualType(te1.carTE, te2.carTE, exp), () =>
            checkEqualType(te1.cdrTE, te2.cdrTE, exp));
    }

    // Structural check for procedures
    if (te1.tag === "ProcTExp" && te2.tag === "ProcTExp") {
        if (te1.paramTEs.length !== te2.paramTEs.length) {
            return bind(unparseTExp(te1), (te1Str: string) =>
                bind(unparseTExp(te2), (te2Str: string) =>
                    bind(unparse(exp), (expStr: string) =>
                        makeFailure<true>(`Incompatible procedure types: ${te1Str} and ${te2Str} in ${expStr}`))));
        }
        const paramChecks = zipWithResult((p1, p2) => checkEqualType(p1, p2, exp), te1.paramTEs, te2.paramTEs);
        return bind(paramChecks, () => checkEqualType(te1.returnTE, te2.returnTE, exp));
    }

    // Fallback: check for deep equality
    return equals(te1, te2) ? makeOk(true) :
        bind(unparseTExp(te1), (te1: string) =>
            bind(unparseTExp(te2), (te2: string) =>
                bind(unparse(exp), (exp: string) =>
                    makeFailure<true>(`Incompatible types: ${te1} and ${te2} in ${exp}`))));
};

/**
 * Computes the type of a concrete fully-typed expression string.
 */
export const L5typeof = (concreteExp: string): Result<string> =>
    bind(p(concreteExp), (x) =>
        bind(parseL5Exp(x), (e: Exp) =>
            bind(typeofExp(e, makeEmptyTEnv()), unparseTExp)));

/**
 * Computes the type of an L5 AST expression, traversing the AST and checking types
 * according to the expression type.
 * All variables and procedures must be explicitly typed in the program.
 */
export const typeofExp = (exp: Parsed, tenv: TEnv): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
        isBoolExp(exp) ? makeOk(typeofBool(exp)) :
            isStrExp(exp) ? makeOk(typeofStr(exp)) :
                isPrimOp(exp) ? typeofPrim(exp) :
                    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
                        isIfExp(exp) ? typeofIf(exp, tenv) :
                            isProcExp(exp) ? typeofProc(exp, tenv) :
                                isAppExp(exp) ? typeofApp(exp, tenv) :
                                    isLetExp(exp) ? typeofLet(exp, tenv) :
                                        isLetrecExp(exp) ? typeofLetrec(exp, tenv) :
                                            isDefineExp(exp) ? typeofDefine(exp, tenv) :
                                                isProgram(exp) ? typeofProgram(exp, tenv) :
                                                    isLitExp(exp) ? typeofLitExp(exp) :
                                                        makeFailure(`Unknown type: ${format(exp)}`);

/**
 * Computes the type of a sequence of expressions, returning the type of the last.
 * Pre-condition: exps is not empty.
 */
export const typeofExps = (exps: List<Exp>, tenv: TEnv): Result<TExp> =>
    isNonEmptyList<Exp>(exps) ?
        isEmpty(rest(exps)) ? typeofExp(first(exps), tenv) :
            bind(typeofExp(first(exps), tenv), _ => typeofExps(rest(exps), tenv)) :
        makeFailure(`Unexpected empty list of expressions`);

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();
// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();
// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

/**
 * Returns the type of a primitive operator.
 * Includes support for cons, car, cdr, and polymorphic predicates.
 */
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

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
                                                                                    (p.op === 'cons') ? parseTE('(T1 * T2 -> (Pair T1 T2))') :
                                                                                        (p.op === 'car') ? parseTE('((Pair T1 T2) -> T1)') :
                                                                                            (p.op === 'cdr') ? parseTE('((Pair T1 T2) -> T2)') :
                                                                                                makeFailure(`Primitive not yet implemented: ${p.op}`);

/**
 * Computes the type of an if-expression.
 * Ensures the test is boolean and both branches have the same type.
 */
export const typeofIf = (ifExp: IfExp, tenv: TEnv): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv);
    const thenTE = typeofExp(ifExp.then, tenv);
    const altTE = typeofExp(ifExp.alt, tenv);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp));
    const constraint2 = bind(thenTE, (thenTE: TExp) =>
        bind(altTE, (altTE: TExp) =>
            checkEqualType(thenTE, altTE, ifExp)));
    return bind(constraint1, (_c1: true) =>
        bind(constraint2, (_c2: true) =>
            thenTE));
};

/**
 * Computes the type of a procedure (lambda) expression.
 * Checks that the body matches the annotated return type.
 */
export const typeofProc = (proc: ProcExp, tenv: TEnv): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv), (body: TExp) =>
        checkEqualType(body, proc.returnTE, proc));
    return bind(constraint1, _ => makeOk(makeProcTExp(argsTEs, proc.returnTE)));
};

/**
 * Computes the type of an application expression.
 * Handles primitive ops (cons, car, cdr) specially for pairs.
 * Otherwise, checks that the rator is a procedure and argument types match.
 */
export const typeofApp = (app: AppExp, tenv: TEnv): Result<TExp> => {
    if (isPrimOp(app.rator)) {
        if (app.rator.op == 'cons')
            return bind(typeofExp(app.rands[0], tenv), (carTE: TExp) =>
                bind(typeofExp(app.rands[1], tenv), (cdrTE: TExp) =>
                    makeOk(makePairTExp(carTE, cdrTE))));
        else if (app.rator.op == 'car') {
            if (isVarRef(app.rands[0])) {
                return bind(applyTEnv(tenv, app.rands[0].var), (pairTE: TExp) => isPairTExp(pairTE) ? makeOk(pairTE.carTE) :
                    makeFailure<TExp>(`car applied to non-pair: ${unparse(app.rands[0])}`));
            }
            else {
                return bind(typeofExp(app.rands[0], tenv), (pairTE: TExp) =>
                    isPairTExp(pairTE) ? makeOk(pairTE.carTE) :
                        makeFailure<TExp>(`car applied to non-pair: ${unparse(app.rands[0])}`));
            }
        }
        else if (app.rator.op == 'cdr') {
            if (isVarRef(app.rands[0])) {
                return bind(applyTEnv(tenv, app.rands[0].var), (pairTE: TExp) => isPairTExp(pairTE) ? makeOk(pairTE.cdrTE) :
                    makeFailure<TExp>(`cdr applied to non-pair: ${unparse(app.rands[0])}`));
            }
            else {
                return bind(typeofExp(app.rands[0], tenv), (pairTE: TExp) =>
                    isPairTExp(pairTE) ? makeOk(pairTE.cdrTE) :
                        makeFailure<TExp>(`cdr applied to non-pair: ${unparse(app.rands[0])}`));
            }
        }
    }
    return bind(typeofExp(app.rator, tenv), (ratorTE: TExp) => {
        if (!isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                bind(unparse(app), (exp: string) =>
                    makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv), (typeOfRand: TExp) =>
            checkEqualType(typeOfRand, trand, app)),
            app.rands, ratorTE.paramTEs);
        return bind(constraints, _ => makeOk(ratorTE.returnTE));
    });
}

/**
 * Computes the type of a let expression.
 * Checks that binding values match their annotated types.
 */
export const typeofLet = (exp: LetExp, tenv: TEnv): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv), (typeOfVal: TExp) =>
        checkEqualType(varTE, typeOfVal, exp)),
        varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv)));
};

/**
 * Computes the type of a letrec expression.
 * Only supports binding of procedures.
 */
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (!allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${format(exp)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
        paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) =>
        zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody));
};

/**
 * Computes the type of a define expression.
 * Checks that the value matches the annotated type.
 */
export const typeofDefine = (exp: DefineExp, tenv: TEnv): Result<VoidTExp> => {
    const result = typeofExp(exp.val, tenv);
    if (isOk(result)) {
        const varTE = exp.var.texp;
        const valTE = result.value;
        const constraint = checkEqualType(varTE, valTE, exp);
        return bind(constraint, _ => makeOk(makeVoidTExp()));
    }
    return makeFailure("Type mismatch");
};

/**
 * Computes the type of a program.
 * The type of a program is the type of the last expression, after threading the environment through all definitions.
 */
export const typeofProgram = (exp: Program, tenv: TEnv): Result<TExp> => {
    const processExp = ([env, _]: [TEnv, Result<TExp>], e: Exp): [TEnv, Result<TExp>] => {
        if (isDefineExp(e)) {
            const valType = typeofExp(e.val, env);
            if (valType.tag === "Failure") return [env, valType];
            const constraint = checkEqualType(e.var.texp, valType.value, e);
            if (constraint.tag === "Failure") return [env, constraint];
            const newEnv = makeExtendTEnv([e.var.var], [e.var.texp], env);
            return [newEnv, makeOk(makeVoidTExp())];
        } else {
            const texp = typeofExp(e, env);
            return [env, texp];
        }
    };

    if (!("exps" in exp)) {
        return makeFailure("Expression is not a Program") as Result<TExp>;
    }

    if (exp.exps.length === 0) {
        return makeFailure("Empty program") as Result<TExp>;
    }

    const [, lastType] = exp.exps.reduce(
        processExp,
        [tenv, makeFailure("Empty program") as Result<TExp>]
    );
    return lastType;
};

/**
 * Computes the type of a concrete fully-typed program string.
 */
export const L5programTypeof = (concreteExp: string): Result<string> =>
    bind(parseL5(concreteExp), (parsedProgram) =>
        isProgram(parsedProgram)
            ? bind(typeofProgram(parsedProgram, makeEmptyTEnv()), (te) =>
                unparseTExp(te))
            : makeFailure("Not a program")
    );

/**
 * Computes the type of a literal (quoted) expression.
 * Handles quoted pairs, numbers, booleans, symbols, and empty lists.
 * Quoted symbols and empty lists are typed as TVar("literal").
 * Quoted pairs are recursively typed as PairTExp.
 * Top-level atoms are always typed as "literal".
 */
const typeofLitExp = (le: LitExp): Result<TExp> => {
    // map an *inner* S-exp value to its TE
    const sexpToTExp = (v: SExpValue): TExp =>
        isCompoundSExp(v)
            // if the first element is the symbol 'quote, treat the
            // whole (quote …) form as an atomic literal.
            ? (isSymbolSExp(v.val1) && v.val1.val === "quote")
                ? makeTVar("literal")
                : makePairTExp(sexpToTExp(v.val1), sexpToTExp(v.val2))
            : isSymbolSExp(v) || isEmptySExp(v)
                ? makeTVar("literal")
                : typeof v === "number"
                    ? makeNumTExp()
                    : typeof v === "boolean"
                        ? makeBoolTExp()
                        : typeof v === "string"
                            ? makeStrTExp()
                            : makeTVar("literal");

    // *Top-level* atoms are always typed as the polymorphic “literal”
    return makeOk(
        isCompoundSExp(le.val) ? sexpToTExp(le.val)
            : makeTVar("literal")
    );
};

/**
 * Helper: recognize type variable names (e.g., "T", "T1", "T2").
 * Used to distinguish between polymorphic type variables and literals.
 */
const isTypeVarName = (s: string): boolean =>
    /^T\d*$/.test(s);

// ...end of file...

