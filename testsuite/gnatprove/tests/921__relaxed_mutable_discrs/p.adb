procedure P with SPARK_Mode is
  type Some_Enum is (One, Two);

   type Other_T (E : Some_Enum := One) is record
      C : Integer;
      case E is
         when One =>
            F : Integer;
         when Two =>
            G : Integer;
      end case;
   end record
      with Relaxed_Initialization;

   type Test_T is record
      A : Integer;
      B : Other_T;
   end record
      with Relaxed_Initialization;

   procedure Init_Other (Flavor : Some_Enum; O : out Other_T)
   with
      Relaxed_Initialization => O,
      Pre => not O'Constrained,
      Post => O'Initialized;

   procedure Init_Other (Flavor : Some_Enum; O : out Other_T)
   is
   begin
      case Flavor is
         when One =>
            O := (E => One, F => 2, C => 3);
         when Two =>
            O := (E => Two, G => 4, C => 5);
      end case;
   end Init_Other;

   procedure Init_Test_Fails (T : out Test_T) with Global => null
   is
   begin
      T.A := 1;
      Init_Other (One, T.B);
   end Init_Test_Fails;
begin
   null;
end;
