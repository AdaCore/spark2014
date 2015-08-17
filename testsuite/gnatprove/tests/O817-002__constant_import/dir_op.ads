package Dir_Op is

   Dir_Sep : constant Character;

private

  pragma Import (C, Dir_Sep, "__gnat_dir_separator");
end Dir_Op;
