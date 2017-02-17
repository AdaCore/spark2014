package body Pkg_A
is


   function Do_Something (X : Integer) return Integer is (X * 2);

begin

   Y := Do_Something (Integer'Last);

end Pkg_A;
