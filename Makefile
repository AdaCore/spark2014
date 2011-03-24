all:
	make -C gnat_backends/why
	make -C gnatprove

all-nightly:
	make -C gnat_backends/why gnat1
	make -C gnatprove

clean:
	make -C gnat_backends/why clean
	make -C gnatprove clean
