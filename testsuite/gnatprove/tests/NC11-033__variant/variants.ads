package Variants with
  SPARK_Mode
is
   type E is (A, B);
   type T (C : E := A) is record
      case C is
         when A =>
            D : Integer;
         when B =>
            E : Integer;
      end case;
   end record;
   subtype TA is T(A);
   subtype TB is T(B);

   procedure Test (X : T; Y : in out TA; Z : out TB) with
     Depends => (Y => X, Z => Y);

end Variants;
