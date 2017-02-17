package P is
   type T is new Integer;
   function "<"  (Left, Right : T) return Boolean;
   pragma Import (Ada, "<");

   function Compare (Left, Right : T) return Boolean
     with Post => (if Compare'Result then not (Left = Right));

   function Compare (Left, Right : T) return Boolean is
      (Left < Right);

   function ">" (Left, Right : T) return Boolean
      with Global => null;
   pragma Import (Ada, ">");

   X : Integer;
   pragma Import (CPP, X, "_X");

   procedure Double
      with Convention => C,
           Import     => True,
           Global     => (In_Out => X);

   procedure Triple
      with Convention => Fortran,
           Import     => True;
end;
