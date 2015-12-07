generic

   type Value_Type is range <>;

   Max_Value : Value_Type;

package Prime_And_Coprime_Numbers with
  Abstract_State    => Prime_Data,
  Initializes       => Prime_Data,
  Initial_Condition => Valid_Prime_Data
is
   type Number_List_Type is
      array (Value_Type range 0 .. Max_Value)
      of Boolean;

   type Nearest_Mode is (Up,
                         Down,
                         Absolute);

   ---------------------------------------
   -- Ghost functions used in contracts --
   ---------------------------------------

   function Is_Prime (Value : Value_Type) return Boolean is
     (Value >= 2 and then (for all V in 2 .. Value - 1 => Value mod V /= 0))
   with Ghost;

   function Valid_Prime_Data return Boolean with Ghost;

   function Are_Coprime (V1, V2 : Value_Type) return Boolean is
     (V1 > 0 and then
      V2 > 0 and then
      (for all V in 2 .. Value_Type'Min (V1, V2) =>
         not (V1 mod V = 0 and V2 mod V = 0)))
   with Ghost;

   function Has_True
     (Number_List : Number_List_Type;
      Low, High   : Value_Type) return Boolean
   is (for some V in Low .. High => Number_List (V) = True)
   with
     Ghost,
     Pre => Low in Number_List'Range and High in Number_List'Range;

   function Has_Prime (Low, High : Value_Type) return Boolean with Ghost;

   -----------------------
   -- Program functions --
   -----------------------

   function Initialize_Coprime_List
      (Value : in Value_Type)
      return Number_List_Type
   with
     Pre  => Value >= 2,
     Post =>
       (for all V in Number_List_Type'Range =>
          Initialize_Coprime_List'Result (V) = Are_Coprime (Value, V));

   function Nearest_Number
      (Number_List : in Number_List_Type;
       Mode        : in Nearest_Mode;
       Value       : in Value_Type)
      return Value_Type
   with
     Pre  => Value in Number_List'Range
       and then (case Mode is
                   when Up       => Has_True (Number_List, Value, Number_List'Last),
                   when Down     => Has_True (Number_List, Number_List'First, Value),
                   when Absolute => Has_True (Number_List, Number_List'First, Number_List'Last)),
     Post => Nearest_Number'Result in Number_List'Range
       and then Number_List (Nearest_Number'Result) = True,
     Contract_Cases =>

       --  If Value is one of the valid numbers in the list, return it

       (Number_List (Value) = True => Nearest_Number'Result = Value,

        --  Otherwise, if Mode is Up, return the nearest valid number above
        --  Value

        Number_List (Value) = False and Mode = Up =>
          Nearest_Number'Result > Value
          and then (for all V in Value .. Nearest_Number'Result - 1 =>
                      Number_List (V) = False),

        --  Otherwise, if Mode is Down, return the nearest valid number below
        --  Value

        Number_List (Value) = False and Mode = Down =>
          Nearest_Number'Result < Value
          and then (for all V in Nearest_Number'Result + 1 .. Value =>
                      Number_List (V) = False),

        --  Otherwise, if Mode is Absolute, return the nearest valid number
        --  above or below Value. Ties are not specified.

        Number_List (Value) = False and Mode = Absolute =>
          (for all V in Value_Type'Max (Number_List'First, Value - abs (Value - Nearest_Number'Result) + 1) .. Value =>
             Number_List (V) = False)
             and then
          (for all V in Value .. Value_Type'Min (Number_List'Last, Value + abs (Value - Nearest_Number'Result) - 1) =>
             Number_List (V) = False));

   function Nearest_Prime_Number
      (Value : in Value_Type;
       Mode  : in Nearest_Mode)
      return Value_Type
   with
     Global => (Input => Prime_Data),
     Pre    => Value in Number_List_Type'Range
       and then Valid_Prime_Data
       and then (case Mode is
                   when Up       => Has_Prime (Value, Number_List_Type'Last),
                   when Down     => Has_Prime (Number_List_Type'First, Value),
                   when Absolute => Has_Prime (Number_List_Type'First, Number_List_Type'Last)),
     Post   => Nearest_Prime_Number'Result in Number_List_Type'Range
       and then Is_Prime (Nearest_Prime_Number'Result),
     Contract_Cases =>

       --  If Value is prime, return it

       (Is_Prime (Value) => Nearest_Prime_Number'Result = Value,

        --  Otherwise, if Mode is Up, return the nearest prime number above
        --  Value

        not Is_Prime (Value) and Mode = Up =>
          Nearest_Prime_Number'Result > Value
          and then (for all V in Value .. Nearest_Prime_Number'Result - 1 =>
                      not Is_Prime (V)),

        --  Otherwise, if Mode is Down, return the nearest prime number below
        --  Value

        not Is_Prime (Value) and Mode = Down =>
          Nearest_Prime_Number'Result < Value
          and then (for all V in Nearest_Prime_Number'Result + 1 .. Value =>
                      not Is_Prime (V)),

        --  Otherwise, if Mode is Absolute, return the nearest prime number
        --  above or below Value. Ties are not specified.

        not Is_Prime (Value) and Mode = Absolute =>
          (for all V in Value_Type'Max (Number_List_Type'First, Value - abs (Value - Nearest_Prime_Number'Result) + 1) .. Value =>
             not Is_Prime (V))
             and then
          (for all V in Value .. Value_Type'Min (Number_List_Type'Last, Value + abs (Value - Nearest_Prime_Number'Result) - 1) =>
             not Is_Prime (V)));

end Prime_And_Coprime_Numbers;
