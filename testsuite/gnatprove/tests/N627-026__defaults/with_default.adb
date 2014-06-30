package body With_Default with SPARK_Mode is

   procedure Bad_Scalar (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0; --@RANGE_CHECK:FAIL
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;
      Bad : Scalar_Bad_Default;
   begin
      null;
   end Bad_Scalar;

   procedure OK_Scalar (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0;
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;
      subtype Scalar_No_Default is Natural range C .. Natural'Last;

      Ok_Def : Scalar_With_Default;
      No_Def : Scalar_Bad_Default := Scalar_With_Default (C);
      No_Ini : Scalar_No_Default;
   begin
      pragma Unreferenced (No_Ini);
      pragma Assert (Ok_Def = 0);
   end OK_Scalar;

   procedure Bad_Array1 (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0; --@RANGE_CHECK:FAIL
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;
      type Array_Bad_Default1 is array (Positive range <>) of Scalar_Bad_Default;
      Bad : Array_Bad_Default1 (1 .. 100);
   begin
      null;
   end Bad_Array1;

   procedure Bad_Array2 (C : Natural) is
      subtype Scalar_No_Default is Natural range C .. Natural'Last;
      type Array_Bad_Default2 is array (Positive range <>) of Scalar_No_Default
        with Default_Component_Value => 0; --@RANGE_CHECK:FAIL
      Bad : Array_Bad_Default2 (1 .. 100);
   begin
      null;
   end Bad_Array2;

   procedure OK_Array (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0;
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;
      subtype Scalar_No_Default is Natural range C .. Natural'Last;
      type Array_With_Default1 is array (Positive range <>) of Scalar_With_Default;
      type Array_With_Default2 is array (Positive range <>) of Natural
        with Default_Component_Value => 1;
      type Array_With_Default3 is array (Positive range <>) of Scalar_Bad_Default
        with Default_Component_Value => 2;
      type Array_No_Default is array (Positive range <>) of Natural;
      type Array_Bad_Default1 is array (Positive range <>) of Scalar_Bad_Default;
      type Array_Bad_Default2 is array (Positive range <>) of Scalar_No_Default
        with Default_Component_Value => 0;

      Empty1 : Array_Bad_Default1 (1 .. 0);
      Empty2 : Array_Bad_Default2 (1 .. 0);
      No_Def : Array_Bad_Default2 := (1 .. 100 => C);
      No_Ini : Array_No_Default (1 .. 100);
      All_0  : Array_With_Default1 (1 .. 100);
      All_1  : Array_With_Default2 (1 .. 100);
      All_2  : Array_With_Default3 (1 .. 100);
   begin
      pragma Unreferenced (No_Ini);
      pragma Assert (All_0 (1) = 0);
      pragma Assert (All_1 (1) = 1);
      pragma Assert (All_2 (1) = 2);
   end OK_Array;

   procedure Bad_Record1 (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0;
      subtype Scalar_No_Default is Natural range C .. Natural'Last;

      type Simple_Rec is record
         F1 : Scalar_With_Default;
         F2 : Scalar_No_Default := 0; --@RANGE_CHECK:FAIL
      end record;

      Bad : Simple_Rec;
   begin
      null;
   end Bad_Record1;

   procedure Bad_Record2 (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0; --@RANGE_CHECK:FAIL
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;

      type Rec_With_Discr (B : Boolean) is record
         case B is
            when True =>
               F1 : Scalar_With_Default;
            when False =>
               F2 : Scalar_Bad_Default;
         end case;
      end record;

      Bad : Rec_With_Discr (False);
   begin
      null;
   end Bad_Record2;

   procedure Bad_Record3 (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0; --@RANGE_CHECK:FAIL
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;

      type Rec_With_Bad_Discr (B : Boolean := False) is record
         case B is
            when True =>
               F1 : Scalar_With_Default;
            when False =>
               F2 : Scalar_Bad_Default;
         end case;
      end record;

      Bad : Rec_With_Bad_Discr;
   begin
      null;
   end Bad_Record3;

   procedure OK_Record (C : Natural) is
      type Scalar_With_Default is new Natural with Default_Value => 0;
      subtype Scalar_Bad_Default is Scalar_With_Default range
        Scalar_With_Default (C) .. Scalar_With_Default'Last;
      subtype Scalar_No_Default is Natural range C .. Natural'Last;

      type Simple_Rec is record
         F1 : Scalar_With_Default;
         F2 : Scalar_No_Default := C;
      end record;

      type Rec_With_Discr (B : Boolean) is record
         case B is
            when True =>
               F1 : Scalar_With_Default;
            when False =>
               F2 : Scalar_Bad_Default;
         end case;
      end record;

      type Rec_With_Default_Discr (B : Boolean := True) is record
         case B is
            when True =>
               F1 : Scalar_With_Default;
            when False =>
               F2 : Scalar_Bad_Default;
         end case;
      end record;

      type Rec_With_Bad_Discr (B : Boolean := False) is record
         case B is
            when True =>
               F1 : Scalar_With_Default;
            when False =>
               F2 : Scalar_Bad_Default;
         end case;
      end record;

      type Rec_With_Ok_Discr (B : Boolean := False) is record
         case B is
            when True =>
               F1 : Scalar_With_Default;
            when False =>
               F3 : Scalar_Bad_Default := Scalar_With_Default (C);
         end case;
      end record;

      No_Def : Rec_With_Bad_Discr := (B => False, F2 => Scalar_With_Default (C));
      Simple : Simple_Rec;
      W_Disc : Rec_With_Discr (True);
      W_D_Di : Rec_With_Default_Discr;
      W_O_Di : Rec_With_Ok_Discr;
   begin
      pragma Assert (Simple.F1 = 0);
      pragma Assert (Simple.F2 = C);
      pragma Assert (W_Disc.F1 = 0);
      pragma Assert (W_D_Di.F1 = 0);
      pragma Assert (not W_O_Di.B);
      pragma Assert (W_O_Di.F3 = Scalar_With_Default (C));
   end OK_Record;

   procedure Bad_Nested_Defaults1 (C : Natural) is
      type Empty_Rec (D : Positive := C) is null record; --@RANGE_CHECK:FAIL
      type Non_Init is record
         E : Empty_Rec;
         F : Natural;
      end record;

      Bad : Non_Init;
   begin
      null;
   end Bad_Nested_Defaults1;

   procedure Bad_Nested_Defaults2 (C : Natural) is
      type Empty_Rec (D : Positive := C) is null record; --@RANGE_CHECK:FAIL
      type My_Array is array (Positive range <>) of Empty_Rec;
      type Non_Init is record
         E : My_Array (1 .. 100);
         F : Natural;
      end record;

      Bad : Non_Init;
   begin
      null;
   end Bad_Nested_Defaults2;

   procedure Ok_Nested_Defaults (C : Natural) is
      type Empty_Rec1 (D : Positive := C) is null record;
      type My_Array1 is array (Positive range <>) of Empty_Rec1;
      type Non_Init1 is record
         E : My_Array1 (1 .. 0);
         F : Natural;
      end record;

      type Empty_Rec2 (D : Positive := 1) is null record;
      type My_Array2 is array (Positive range <>) of Empty_Rec2;
      type Non_Init2 is record
         E : My_Array2 (1 .. 100);
         F : Natural;
      end record;

      Empty : Non_Init1;
      All_1 : Non_Init2;
   begin
      pragma Assert (All_1.E (1).D = 1);
   end Ok_Nested_Defaults;

end;
