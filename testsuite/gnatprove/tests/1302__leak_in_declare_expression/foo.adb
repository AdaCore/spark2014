pragma Ada_2022;
procedure Foo with SPARK_Mode is
   type Int_Acc is not null access Integer;

   function Deep_Copy (X : Int_Acc) return Int_Acc with
     Import, Global => null, Post => X.all = Deep_Copy'Result.all;

   procedure Incr_1 (X : in out Int_Acc) with
     Pre  => X.all < Integer'Last,
     Post => (Static => X.all = Deep_Copy (X)'Old.all + 1);

   procedure Incr_2 (X : in out Int_Acc) with
     Pre  => X.all < Integer'Last,
     Post => (Static => (declare Old_X : constant Int_Acc := Deep_Copy (X)'Old;
                         begin X.all = Old_X.all + 1));

   procedure Incr_1 (X : in out Int_Acc) is
   begin
      X.all := X.all + 1;
   end Incr_1;

   procedure Incr_2 (X : in out Int_Acc) is
   begin
      X.all := X.all + 1;
   end Incr_2;

begin
   null;
end;
