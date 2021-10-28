# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax.py

"""Syntactic handling of first-order formulas and terms."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union

from logic_utils import fresh_variable_name_generator, frozen

from propositions.syntax import Formula as PropositionalFormula, \
                                is_variable as is_propositional_variable

class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context."""

    def __init__(self, variable_name: str) -> None:
        """Initializes a `ForbiddenVariableError` from its offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it was to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name

def is_constant(s: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return  (((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd'))
             and s.isalnum()) or s == '_'

def is_variable(s: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()

def is_function(s: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()

@frozen
class Term:
    """An immutable first-order term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str,
                 arguments: Optional[Sequence[Term]] = None) -> None:
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        # Task 7.1

        if is_constant(self.root) or is_variable(self.root):
            return self.root

        to_return = self.root
        to_return += "("

        for index , arg in enumerate(self.arguments):
            to_return += arg.__repr__()
            if index != len(self.arguments) - 1:
                to_return += ","

        to_return += ")"

        return to_return


    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.3.1

        if is_variable(s[0]):
            if len(s) == 1:
                return Term(s[0]), ""
            flag = True
            index = 1
            for index in range(1, len(s)):
                if s[index].isalnum():
                    continue
                else:
                    flag = False
                    break
            if flag:
                return Term(s[:index + 1]), ""
            return Term(s[:index]), s[index:]

        if is_constant(s[0]):
            if len(s) == 1:
                return Term(s[0]), ""

            if s[0] == "_" and len(s) > 1:
                return Term(s[0]), s[1:]

            flag = True
            index = 1
            for index in range(1, len(s)):
                if s[index].isalnum():
                    continue
                else:
                    flag = False
                    break
            if flag:
                return Term(s[:index + 1]), ""
            return Term(s[:index]), s[index:]

        index_open = s.find("(")
        index = index_open + 1
        function_name = s[:index_open]
        counter = 1
        opens = []
        opens.append(index_open)
        closed = []
        last_one = index_open

        terms = []

        while (index < len(s)):

            if s[index] == "(":
                counter += 1
                opens.append(index)
            elif s[index] == ")":
                counter -= 1
                closed.append(index)

            elif s[index] == "," and len(opens) < len(closed) + 2 : # check if in function
                terms.append(Term.parse_prefix(s[last_one + 1 : index])[0])
                last_one = index

            if counter == 0:
                break

            index += 1

        terms.append(Term.parse_prefix(s[last_one + 1 : index])[0])
        return Term(function_name, terms), s[index + 1:]


    @staticmethod
    def parse(s: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            s: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        # Task 7.3.2

        return Term.parse_prefix(s)[0]

    def __helper_constants__(self, constant) -> Set[str]:
        if is_variable(self.root):
            return constant
        elif is_constant(self.root):
            constant.add(self.root)
        else:
            for arg in self.arguments:
                constant = arg.__helper_constants__(constant)
        return constant

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        return self.__helper_constants__(set())

        # Task 7.5.1

    def __helper_variables__(self, variables) -> Set[str]:

        if is_constant(self.root):
            return variables
        else:
            if is_variable(self.root):
                variables.add(self.root)
            else:
                for arg in self.arguments:
                    variables = arg.__helper_variables__(variables)
        return variables

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        return self.__helper_variables__(set())
        # Task 7.5.2

    def __helper_functions__(self, functions) -> Set[Tuple[str, int]]:
        if is_variable(self.root) or is_constant(self.root):
            return functions
        if is_function(self.root):
            functions.add((self.root, len(self.arguments)))
            for arg in self.arguments:
                functions = arg.__helper_functions__(functions)
        return functions

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        return self.__helper_functions__(set())
        # Task 7.5.3

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.1

def is_equality(s: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return s == '='

def is_relation(s: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()

def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s == '&' or s == '|' or s == '->'

def is_quantifier(s: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return s == 'A' or s == 'E'

@frozen
class Formula:
    """An immutable first-order formula in tree representation, composed from
    relation names applied to first-order terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the the root, if
                the root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate           
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        # Task 7.2

        if is_equality(self.root):
            return self.arguments[0].__repr__() + "=" + self.arguments[1].__repr__()

        if is_relation(self.root):
            to_return = self.root + "("
            for index, arg in enumerate(self.arguments):
                to_return += arg.__repr__()
                if index != len(self.arguments) - 1:
                    to_return += ","
            to_return += ")"
            return to_return

        if is_unary(self.root):
            return "~" + self.first.__repr__()

        if is_binary(self.root):
            first = self.first.__repr__()
            secd = self.second.__repr__()
            return "(" + first + self.root + secd + ")"

        if is_quantifier(self.root):
            return self.root + self.variable + "[" + self.predicate.__repr__() + "]"


    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)
        
    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        # Task 7.4.1

        index = 0
        open_number = 0
        close_number = 0
        square_open = 0
        square_close = 0
        operator_number = 0
        index_close = 0
        index_operator = 0
        count_par = 0
        to_return = ""
        relation = None

        if is_unary(s[0]):
            formula = Formula.parse_prefix(s[1:])
            return Formula("~", formula[0]), formula[1]

        if is_quantifier(s[0]):
            var = s[1:s.find("[")]
            formula =  Formula.parse_prefix(s[s.find("[")+1:])
            return Formula(s[0],var,formula[0]),formula[1][1:]

        if is_relation(s[0]):
            relation = s[0:s.find("(")]
            index = s.find("(")

        if s[index] == "(":
            while (index < len(s)):

                if s[index] == "(":
                    open_number += 1
                    count_par += 1
                elif s[index] == ")":
                    close_number += 1
                    count_par -= 1
                    index_close = index
                elif is_binary(s[index]):
                    operator_number += 1
                    if count_par == 1:
                        index_operator = index
                elif index + 1 < len(s) and s[index:index + 2] == "->":
                    operator_number += 1
                    index += 1
                    if count_par == 1:
                        index_operator = index
                index += 1

                if open_number == close_number and square_open == square_close:
                    to_return = s[index_close + 1:]
                    break

            if index_close != len(s) - 1:
                to_return = s[index_close + 1:]

            if relation is not None:
                terms = []
                counter = 0
                opens = []
                closed = []
                last_one = s.find("(")
                i = last_one

                while (i < len(s)):

                    if s[i] == "(":
                        counter += 1
                        opens.append(index)
                    elif s[i] == ")":
                        counter -= 1
                        closed.append(index)

                    elif s[i] == "," and len(opens) < len(closed) + 2:  # check if in function
                        terms.append(Term.parse_prefix(s[last_one + 1: i])[0])
                        last_one = i

                    if counter == 0:
                        break

                    i += 1
                if s[last_one + 1 : i] != "":
                    terms.append(Term.parse_prefix(s[last_one + 1: i])[0])
                return Formula(relation, terms), to_return

            if s[index_operator] == ">":
                return Formula("->", Formula.parse_prefix(s[1:index_operator - 1])[0],
                               Formula.parse_prefix(s[index_operator + 1:index_close])[0]), to_return

            return Formula(s[index_operator], Formula.parse_prefix(s[1:index_operator])[0],
                           Formula.parse_prefix(s[index_operator + 1:index_close])[0]), to_return


        else:
            split_equal = s.split("=")
            first = Term.parse_prefix(split_equal[0])[0]
            scd = Term.parse_prefix(split_equal[1])
            return_to = scd[1]
            if len(split_equal)> 2:
                for i in range(2, len(split_equal)):
                    if i != len(split_equal):
                        return_to += "="
                    return_to += split_equal[i]
            return Formula("=",[Term.parse(first.__repr__()), Term.parse(scd[0].__repr__())]),return_to



    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2

        return Formula.parse_prefix(s)[0]

    def __helper_constants__(self, constants) -> Set[str]:
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                constants = arg.__helper_constants__(constants)
        if is_unary(self.root):
            constants = self.first.__helper_constants__(constants)
        if is_binary(self.root):
            constants = self.first.__helper_constants__(constants)
            constants = self.second.__helper_constants__(constants)
        if is_quantifier(self.root):
            constants = self.predicate.__helper_constants__(constants)
        return constants

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        return self.__helper_constants__(set())
        # Task 7.6.1

    def __helper_variables__(self, variables) -> Set[str]:
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                variables = arg.__helper_variables__(variables)
        if is_unary(self.root):
            variables = self.first.__helper_variables__(variables)
        if is_binary(self.root):
            variables = self.first.__helper_variables__(variables)
            variables = self.second.__helper_variables__(variables)
        if is_quantifier(self.root):
            for var in self.variable:
                variables.add(var)
            variables = self.predicate.__helper_variables__(variables)
        return variables

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        return self.__helper_variables__(set())
        # Task 7.6.2

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of all variable names used in the current formula not only
            within a scope of a quantification on those variable names.
        """
        # Task 7.6.3

        if is_equality(self.root):
            bad_variables1 = self.arguments[0].variables()
            bad_variables2 = self.arguments[1].variables()
            return bad_variables1.union(bad_variables2)

        if is_quantifier(self.root):
            bad_variables = set()
            for var in self.variable:
                bad_variables.add(var)
            goods = self.predicate.free_variables()
            return goods.difference(bad_variables)

        if is_unary(self.root):
            return self.first.free_variables()

        if is_binary(self.root):
            first_values = self.first.free_variables()
            second_values = self.second.free_variables()
            return first_values.union(second_values)

        if is_relation(self.root):
            values = set()
            for arg in self.arguments:
                values.update(arg.variables())
            return values

    def __helper_functions__(self, functions) -> Set[Tuple[str, int]]:
        if is_equality(self.root) or is_relation(self.root):
            for arg in self.arguments:
                functions = arg.__helper_functions__(functions)
        if is_unary(self.root):
            functions = self.first.__helper_functions__(functions)
        if is_binary(self.root):
            functions = self.first.__helper_functions__(functions)
            functions = self.second.__helper_functions__(functions)
        if is_quantifier(self.root):
            functions = self.predicate.__helper_functions__(functions)
        return functions

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        return self.__helper_functions__(set())

        # Task 7.6.4

    def __helper_relations__(self, relations) -> Set[Tuple[str, int]]:
        if is_relation(self.root):
            relations.add((self.root, len(self.arguments)))
        if is_unary(self.root):
            relations = self.first.__helper_relations__(relations)
        if is_binary(self.root):
            relations = self.first.__helper_relations__(relations)
            relations = self.second.__helper_relations__(relations)
        if is_quantifier(self.root):
            relations = self.predicate.__helper_relations__(relations)
        return relations

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        return self.__helper_relations__(set())
        # Task 7.6.5


    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> \
                Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)
        # Task 9.2

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a map from each atomic
            propositional formula to the subformula for which it was
            substituted.
        """
        # Task 9.6

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a first-order formula from a propositional skeleton and a
        substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute.
            substitution_map: a map from each atomic propositional subformula
                of the given skeleton to a first-order formula.

        Returns:
            A first-order formula obtained from the given propositional skeleton
            by substituting each atomic propositional subformula with the formula
            mapped to it by the given map.
        """
        for key in substitution_map:
            assert is_propositional_variable(key)
        # Task 9.10
