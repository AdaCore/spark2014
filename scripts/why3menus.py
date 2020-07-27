import sys
import re
import json

""" This file is used to generate a python file that only contains the list of
    transformations/provers. This file/list is then used inside the spark
    plugin for GPS to create the menu of interactive proofs. The way those
    transformations are generated is through a call to
    "why3ide --list-transform" -> stdin: this generation is only done on
    developper's machines during compilation"""

out_file = open(sys.argv[1], 'w')

list_transforms = []

# In transf_list, a single element list means a lone transformation, a
# multi-element list means the first element is the title of a submenu.
# This is an idealized transformation list. Comments explain why groups are
# made.
ideal_transf_list = [
    ["Provers",  # Semantic -> provers
     "altergo", "z3", "cvc4"],
    ["abstract",  # Prefix -> abstract
     "abstract__quantifiers", "abstract__unknown__lsymbols"],
    ["apply"],
    ["assert",  # Semantic -> assert
     "assert", "cut"],
    ["case"],
    ["remove",  # Semantic -> remove
     "clear__but", "remove", "remove__rec", "remove__triggers"],
    ["compute",  # Semantic -> computations
     "compute__hyp", "compute__hyp__specified", "compute__in__goal",
     "compute__specified", "step", "steps"],
    ["congruence"],
    ["destruct",  # Semantic -> destruct
     "destruct", "destruct__rec", "destruct__term",
     "destruct__term__subst"],
    ["eliminate",  # Prefix -> eliminate
     "eliminate__algebraic", "eliminate__builtin",
     "eliminate__definition", "eliminate__definition__func",
     "eliminate__definition__pred", "eliminate__epsilon",
     "eliminate__if", "eliminate__if__fmla", "eliminate__if__term",
     "eliminate__inductive", "eliminate__let", "eliminate__let__fmla",
     "eliminate__let__term", "eliminate__literal", "eliminate__match",
     "eliminate__mutual__recursion", "eliminate__negative__constants",
     "eliminate__non__lambda__epsilon",
     "eliminate__non__lambda__set__epsilon",
     "eliminate__non__struct__recursion",
     "eliminate__projections", "eliminate__quantifiers",
     "eliminate__recursion", "eliminate__symbol",
     "eliminate__unused__hypo", "lift__epsilon"],
    ["exists"],
    ["explode__record__param"],
    ["filter__trigger",  # Prefix -> filter
     "filter__trigger", "filter__trigger__builtin",
     "filter__trigger__no__predicate"],
    ["fold__defs"],
    ["revert",  # Semantic -> revert
     "generalize__introduced", "revert"],
    ["hide",  # Semantic -> hide
     "hide", "hide__and__clear"],
    ["induction",  # Semantic -> induction
     "induction", "induction__arg__pr", "induction__arg__ty__lex",
     "induction__pr", "induction__ty__lex"],
    ["inline",  # Semantic -> inline
     "inline__all", "inline__goal", "inline__tagged",
     "inline__trivial"],
    ["instantiate",  # Semantic -> instantiate
     "instantiate", "inst__rem"],
    ["intros",  # Semantic -> intros
     "introduce__exists", "introduce__premises", "intros",
     "intros__n"],
    ["inversion",  # Semantic -> inversion
     "inversion__arg__pr", "inversion__pr"],
    ["left right",  # Semantic -> left/right
     "left", "right"],
    ["pose"],
    ["prop__curry"],
    ["rewrite",  # Semantic -> rewrite
     "replace", "rewrite", "rewrite__list"],
    ["simplify",  # Prefix -> simplify
     "simplify__array", "simplify__computations", "simplify__formula",
     "simplify__formula__and__task",
     "simplify__trivial__quantification",
     "simplify__trivial__quantification__in__goal"],
    ["spark__simpl"],
    ["split",  # Prefix -> split
     "split__all__full", "split__all__right", "split__conj",
     "split__conj__axioms", "split__disj", "split__goal__full",
     "split__goal__right", "split__goal__wp__conj", "split__premise__full",
     "split__premise__right", "split__vc"],
    ["subst",  # Prefix -> subst
     "subst", "subst__all"],
    ["unfold"]]

for line in sys.stdin:
    match = re.search(r'^\s*\w+\s*$', line)
    if match:
        line = line.replace(' ', '')
        line = line.replace('\n', '')
        # For GPS reasons, underscore need to be doubled
        line = line.replace('_', '__')
        list_transforms.append(line)
# also add fully supported provers
list_transforms.append("altergo")
list_transforms.append("z3")
list_transforms.append("cvc4")

# This makes sure that in ideal_transf_list, there are only existing
# transformations. If not, an error is returned and people should remove the
# transformation (that was removed in Why3/gnatwhy3)
for sub in ideal_transf_list:
    if len(sub) == 1:
        if sub[0] not in list_transforms:
            print(sub[0])
            # Remove the non-existing transformation from the list
            exit(1)
    else:
        for e in sub[1:]:
            if e not in list_transforms:
                print(e)
                # Remove the non-existing transformation from the list
                exit(1)

sys.stdout = out_file
print(json.dumps(ideal_transf_list))
