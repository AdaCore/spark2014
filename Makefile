all:
	make -C gnat_backends/why
	make -C gnatprove

clean:
	make -C gnat_backends/why clean
	make -C gnatprove clean
