procedure Alloc is
   type E is null record;
   type T (D : Integer := 0) is null record;
   subtype S is T (D => 0);
   type V (D : Integer := 0) is record
      case D is
         when 0 =>
            null;
         when others =>
            C : Integer := 0;
      end case;
   end record;
   subtype F is V (D => 0);
   --  These all are either null records, or become null when the discriminant
   --  is set to zero.

   type PE is access E;
   type PT is access T;
   type PS is access S;
   type PV is access V;
   type PF is access F;

   X : PE := new E;
   Y : PT := new T (D => 0);
   Z : PS := new S;
   Q : PV := new V (D => 0);
   R : PF := new F;
begin
   null;
end;
