package Ring_Buffer with SPARK_Mode is
   Max_Size : constant Natural := 100;
   subtype Length_Range is Integer range 0 .. Max_Size;
   type Nat_Array is array (Positive range <>) of Natural;
   type Model_Type (Length : Length_Range := 0) is record
      Content : Nat_Array (1 .. Length);
   end record with Ghost;
   Model : Model_Type with Ghost;
   function Valid_Model return Boolean with Ghost;
   function Valid_Model (M : Nat_Array) return Boolean with Ghost;

   function Get_Model return Nat_Array with Ghost,
     Post => Valid_Model (Get_Model'Result)
     and Get_Model'Result'First = 1
     and Get_Model'Result'Last in Length_Range;

   procedure Push_Last1 (E : Natural) with
     Pre  => Get_Model'Length < Max_Size,
     Post => Get_Model = Get_Model'Old & E;

   procedure Push_Last (E : Natural) with
     Pre  => Valid_Model and Model.Length < Max_Size,
     Post => Valid_Model and Model.Content = Model.Content'Old & E;

   procedure Pop_First (E : out Natural) with
     Pre  => Valid_Model and Model.Length > 0,
     Post => Valid_Model and E & Model.Content = Model.Content'Old;

   pragma Unevaluated_Use_Of_Old (Allow);

   procedure Pop_When_Available (E : in out Natural) with
     Pre            => Valid_Model,
     Post           => Valid_Model,
     Contract_Cases =>
     (Model.Length > 0 => E & Model.Content = Model.Content'Old,
      others           => Model = Model'Old and E = E'Old);
end Ring_Buffer;
