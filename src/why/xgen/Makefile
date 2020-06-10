# The Why-tree Ada files are automatically generated. This Makefile is used to
# build and generate those files. The main file for generation is xtree.adb. In
# practice, the files that are suffixed by a *-tmpl contain specific keywords
# of the form _@Stuff@_ that are replaced by xtree.
# In particular, to modify the dependencies of one of those files, it is
# necessary to update the -tmpl. To modify a specific node, xtree_sinfo.adb
# should be modified.

.PHONY: all

GENERATED_FILES= \
 why-classes.ads              \
 why-atree.ads                \
 why-atree-accessors.ads      \
 why-atree-builders.ads       \
 why-atree-builders.adb       \
 why-atree-mutators.ads       \
 why-atree-mutators.adb       \
 why-atree-traversal.ads      \
 why-atree-traversal.adb      \
 why-atree-traversal_stub.ads \
 why-atree-traversal_stub.adb \
 why-atree-treepr.ads         \
 why-atree-treepr.adb         \
 why-atree-validity.ads       \
 why-conversions.ads          \
 why-ids.ads                  \
 why-kind_validity.ads        \
 why-opaque_ids.ads           \
 why-unchecked_ids.ads        \
 why-atree-to_json.adb

all:
	gprbuild -j0 -p -Phelpers xtree
	./xtree
	cp $(GENERATED_FILES) ../

clean:
	-rm -rf obj
	-rm -f xtree
	-rm -f $(GENERATED_FILES) gnat_ast.ml
