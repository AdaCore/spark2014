with Type_Pkg;
generic
package Gen is
   use type Type_Pkg.T;
   type Gen_Type is private;
private
   type Gen_Type is new Type_Pkg.T;

   Null_Gen_Type : constant Gen_Type :=
     (A => 0, B => 0);
end;
