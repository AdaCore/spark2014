procedure Test with spark_mode is

   type Rec_Typ (I : Integer := 0) is record
      Comp_0 : Integer := 0;
      Comp_1 : Integer := 1;
      case I is
         when 0 =>
            Comp_2 : Integer := 2;
         when 1 =>
            Comp_3 : Integer;
         when 2 =>
            Comp_4 : Integer := 4;
         when 3 =>
            Comp_5 : Integer;
         when others =>
            Comp_Other : Integer;
      end case;
   end record with Unchecked_Union;

   type Holder (I : Integer := 0) is record
      case I is
         when 0 =>
            Comp_0 : Integer := 1;
         when others =>
            Comp_Other : Rec_Typ (I);
      end case;
   end record with Unchecked_Union;

   procedure Test (X, Y : Holder) is
   begin
      pragma Assert (X.Comp_Other = Y.Comp_Other); -- @UU_RESTRICTIONS
   end;

   H1 : Holder := (I => 1, Comp_Other => (I => 1, others => 1));
   H2 : Holder := (I => 1, Comp_Other => (I => 1, others => 1));
begin
   Test (H1, H2);
end;
