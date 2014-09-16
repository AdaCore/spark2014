package Pkg_B is

   type Widget is record
      X, Y : Natural;
   end record;

   procedure New_Widget (X : out Widget);

end Pkg_B;
