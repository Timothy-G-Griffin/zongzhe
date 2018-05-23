.PHONY: all clean 

all:
	coqc -q -R . CAS  basic.v
	coqc -q -R . CAS  properties.v
	coqc -q -R . CAS  structures.v
	coqc -q -R . CAS  facts.v
	coqc -q -R . CAS  brel_add_constant.v
	coqc -q -R . CAS  bop_add_id.v
	coqc -q -R . CAS  bop_add_ann.v
	coqc -q -R . CAS  brel_reduce.v
	coqc -q -R . CAS  product.v
	coqc -q -R . CAS  reduction_theory.v
	coqc -q -R . CAS  bop_full_reduce.v
	coqc -q -R . CAS  predicate_reduce.v
	coqc -q -R . CAS  reduce_annihilators.v
	coqc -q -R . CAS  reduce_annihilators_semigroup.v
	coqc -q -R . CAS  min_plus_ceiling_reduction.v
	coqc -q -R . CAS  elementary_path.v
	coqc -q -R . CAS  lexicographic_product.v

clean:
	rm -f  *.glob  .*.aux *.vo *.d *~



