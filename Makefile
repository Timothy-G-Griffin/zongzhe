.PHONY: all clean 

all:
	coqc -q -R . CAS  basic.v
	coqc -q -R . CAS  properties.v
	coqc -q -R . CAS  bop_full_reduce.v
	coqc -q -R . CAS  structures.v
	coqc -q -R . CAS  brel_reduce.v
	coqc -q -R . CAS  facts.v
	coqc -q -R . CAS  product.v
	coqc -q -R . CAS  reduction_theory.v
	coqc -q -R . CAS  reduced_semigroup_direct.v
	coqc -q -R . CAS  rsemigroup.v
	coqc -q -R . CAS  simple_examples.v
	coqc -q -R . CAS  reduce_annihilators.v
	coqc -q -R . CAS  predicate_reduce.v
	coqc -q -R . CAS  predicate_reduce_disjoint.v

clean:
	rm -f  *.glob  .*.aux *.vo *.d *~



