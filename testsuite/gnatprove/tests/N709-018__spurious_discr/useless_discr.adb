procedure Useless_Discr with
  SPARK_Mode
is
   type E is (A, B, C, D);

   type T (Discr : E) is tagged record
      Z : Boolean;
      case Discr is
         when A | C =>
            X : Integer;
         when others =>
            Y : Float;
      end case;
   end record;

   V : T(A);
begin
   V.Z := True;
   V.X := 0;
end Useless_Discr;
