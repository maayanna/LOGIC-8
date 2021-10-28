# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *
import copy
from functools import reduce


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]

def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]

def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings
    # Task 8.1

    new_relations = dict()
    new_relations.update(model.relation_meanings)
    for func in model.function_meanings:
        relation_name = function_name_to_relation_name(func)
        new_result = set()
        for tuple_result in model.function_meanings[func]:
            entity = [model.function_meanings[func][tuple_result]]
            for a in tuple_result:
                entity.append(a)
            new_result.add(tuple(entity))
        new_relations[relation_name] = new_result
    new_model = Model(model.universe, model.constant_meanings, new_relations, {})
    return new_model


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings
    # Task 8.2

    new_functions = dict()
    new_relations = dict()
    for relation in model.relation_meanings:
        function_name = relation_name_to_function_name(relation)
        if function_name in original_functions:
            new_result = dict()
            len_arguments = len(model.relation_meanings[relation])
            for tuple_result in model.relation_meanings[relation]:
                len_entity = len(tuple_result) -1
                if len_arguments % len_entity == 0:
                    if len(tuple_result) >= 2:
                        if tuple_result[1:] not in new_result:
                            new_result[tuple_result[1:]] = tuple_result[0]
                        else:
                            return None
                    else:
                        return None
                else:
                    return None
                new_functions[function_name] = new_result
        else:
            new_relations[relation] = model.relation_meanings[relation]
    new_model = Model(model.universe, model.constant_meanings, new_relations, new_functions)
    return new_model


def __helper_compile(term):

    arguments = list()
    list_steps = list()

    for arg in term.arguments:

        if is_function(arg.root):
            term_return, add_to_hel = __helper_compile(arg)
            arguments.append(term_return)
            for add in add_to_hel:
                list_steps.append(add) # all terms compiling
        else:
            arguments.append(arg)

    new_term = Term(next(fresh_variable_name_generator))
    list_steps.append(Formula("=", [new_term, Term(term.root, arguments)]))
    return new_term, list_steps


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)
    # Task 8.3

    new_term, list_helper = __helper_compile(term)
    return list_helper


def __replace_equality(formula):
    # x=y

    compiled_first = list()
    compiled_scd = list()

    if is_function(formula.arguments[0].root):
        compiled_first = compile_term(formula.arguments[0])

    if is_function(formula.arguments[1].root):
        compiled_scd = compile_term(formula.arguments[1])

    arg_first = formula.arguments[0]
    arg_scd = formula.arguments[1]

    if len(compiled_first) != 0:
        arg_first = compiled_first[-1].arguments[0]

    if len(compiled_scd) != 0:
        arg_scd = compiled_scd[-1].arguments[0]

    all_compiled = compiled_first + compiled_scd

    if len(all_compiled) == 0:
        return formula

    new_formula = Formula(formula.root, [arg_first, arg_scd])

    for form in reversed(all_compiled):
        new_lst = list()
        new_lst.append(form.arguments[0])
        for item in list(form.arguments[1].arguments):
            new_lst.append(item)
        new_relation = Formula(function_name_to_relation_name(form.arguments[1].root), new_lst)
        first_return = Formula("->", new_relation, new_formula)
        new_formula = Formula('A', form.arguments[0].root, first_return)

    return new_formula



def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function,arity in formula.functions()}.intersection(
                    {relation for relation,arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'
    # Task 8.4

    if is_unary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first))

    if is_binary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first),
                       replace_functions_with_relations_in_formula(formula.second))

    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))

    if is_variable(formula.root) or is_constant(formula.root):
        return formula

    if is_relation(formula.root):

        args = list()
        list_helper = list()

        for arg in formula.arguments:
            if is_function(arg.root):
                comp = compile_term(arg)
                new_term = comp[-1].arguments[0]
                args.append(new_term)
                for item in comp:
                    list_helper.append(item)
            else:
                args.append(arg)

        new_formula = Formula(formula.root, args)

        if len(list_helper) == 0:
            return formula

        for form in reversed(list_helper):
            new_lst = list()
            new_lst.append(form.arguments[0])
            for item in list(form.arguments[1].arguments):
                new_lst.append(item)
            new_relation = Formula(function_name_to_relation_name(form.arguments[1].root), new_lst)
            first_return = Formula("->", new_relation, new_formula)
            new_formula = Formula('A', form.arguments[0].root, first_return)

        return new_formula

    else: #equality
        return __replace_equality(formula)



def replace_functions_with_relations_in_formulas(formulas:
                                                 AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function,arity in formula.functions()}
                           for formula in formulas]).intersection(
                               set.union(*[{relation for relation,arity in
                                            formula.relations()} for
                                           formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'
    # Task 8.5

    names = list()
    all_formulas = set()

    for formula in formulas:
        for func in formula.functions():
            names.append(func)
        all_formulas.add(replace_functions_with_relations_in_formula(formula))

    to_return = all_formulas

    for func in names:
        args_num = func[1]
        str_ret = ""
        lst_terms = list()
        for index in range(args_num):
            str_ret += "[Ax"
            str_ret += str(index + 1)
            term = "x"
            term += str(index + 1)
            lst_terms.append(term)
        str_ret += "["
        str_ret += "Ez["
        str_ret += str(function_name_to_relation_name(func[0]))
        str_ret += "("
        str_ret += "z"
        str_ret += ","
        for t in lst_terms:
            str_ret += t
            str_ret += ","
        str_ret = str_ret[1:-1]

        str_ret += ")"
        for index in range(args_num + 1):
            str_ret += "]"

        # print(str_ret)
        to_return.add(Formula.parse(str_ret))


        args_num = func[1]
        str_ret = "Ax"
        lst_terms = list()
        for index in range(args_num + 1):
            str_ret += "[Az"
            str_ret += str(index + 1)
            term = "z"
            term += str(index + 1)
            lst_terms.append(term)
        str_ret += "["
        str_ret += "("
        str_ret += "("
        str_scd = ""
        for t in lst_terms:
            str_ret += str(function_name_to_relation_name(func[0]))
            str_ret += "("
            str_ret += t
            str_ret += ","
            str_ret += "x"
            str_ret += ")&"
            str_scd += t
            str_scd += "="
        str_ret = str_ret[0:-1]
        str_scd = str_scd[0:-1]

        str_ret += ")"
        for index in range(args_num + 1):
            str_scd += "]"

        str_full = str_ret + "->" + str_scd + ")"
        # print(str_full)

        to_return.add(Formula.parse(str_full))

    return to_return


def helper_replace_same(formula:Formula):
    if is_equality(formula.root):
        return Formula('SAME', formula.arguments)
    if is_relation(formula.root):
        return formula
    if is_unary(formula.root):
        return Formula(formula.root, helper_replace_same(formula))
    if is_binary(formula.root):
        return Formula(formula.root, helper_replace_same(formula.first), helper_replace_same(formula.second))
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable,helper_replace_same(formula.predicate))

def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation,arity in formula.relations()}
    # Task 8.6

    reflexivity = Formula.parse("Ax[SAME(x,x)]")
    symetry = Formula.parse("Ax[Ay[(SAME(x,y)->SAME(y,x))]]")
    transivity = Formula.parse("Ax[Ay[Az[((SAME(x,y)&SAME(y,z))->SAME(x,z))]]]")
    x_vars = list()
    y_vars = list()
    my_formulas = set()
    for f in formulas:
        my_formulas.add(helper_replace_same(f))
    my_formulas.update({reflexivity,transivity,symetry})
    for f in formulas:
        for rel in f.relations():
            if rel[1]!= 0:
                for i in range(1, rel[1]+1):
                    x_vars.append(Term("x" + str(i)))
                    y_vars.append(Term("y" + str(i)))
                end_f = Formula.parse("SAME(x1,y1)")
                for i in range(1,rel[1]):
                    f2 = Formula.parse("SAME"+"("+ x_vars[i].__repr__()+","+y_vars[i].__repr__()+")")
                    end_f = Formula.parse("("+f2.__repr__() + "&" + end_f.__repr__()+")")

                end_s = Formula('->', Formula(rel[0], x_vars), Formula(rel[0], y_vars))
                end = Formula("->", end_f, end_s)
                # print(end_s.__repr__())
                for i in range(1, rel[1]+1):
                    end = Formula('A', 'x' + str(i), Formula('A', 'y' + str(i), end))
                my_formulas.add(end)
    return my_formulas

def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7

    all_elements = set()
    rel_mean = dict(model.relation_meanings)

    for element in model.universe:
        all_elements.add((element, element))

    rel_mean["SAME"] = all_elements
    model_return = Model(model.universe, model.constant_meanings, rel_mean, model.function_meanings)
    return model_return
    
def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8

    new_dic_same = dict()

    new_rel_meanings = dict(model.relation_meanings)
    new_rel_meanings.pop("SAME")
    univers = set()

    new_cst = dict()
    temp_u = set()

    for couple in model.relation_meanings["SAME"]:
        if couple[0] != couple[1]:
            if couple[0] in new_dic_same.keys():
                new_dic_same[couple[0]].add(couple[1])
            elif couple[1] in new_dic_same.keys():
                new_dic_same[couple[1]].add(couple[0])
            else:
                new_dic_same[couple[0]] = set(couple[1])
                temp_u.add(couple[0])

        else:
            temp_u.add(couple[0])

    for u in temp_u:
        for key, sub in new_dic_same.items():
            if u not in sub:
                univers.add(u)


    for constant, meaning in model.constant_meanings.items():
        if meaning in univers:
            new_cst[constant] = meaning
        for key, value in new_dic_same.items():
            if meaning in value:
                new_cst[constant] = key
                break




    for relation in model.relation_meanings:

        if relation is not "SAME":

            meanings = set()

            for mean in model.relation_meanings[relation]:
                for item in mean:
                    if item in univers:
                        meanings.add(tuple(item))
                    else:
                        for key, value in new_dic_same.items():
                            if item in value:
                                meanings.add(tuple(key))
                                break

            new_rel_meanings[relation] = meanings


    return Model(univers, new_cst, new_rel_meanings, dict())



#TODO fuck la police!!!
