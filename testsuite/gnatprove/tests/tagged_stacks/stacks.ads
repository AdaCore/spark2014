package Stacks with SPARK_Mode is
   Max : constant Natural := 100;
   subtype Less_Than_Max is Natural range 0 .. Max;

   type Element is new Natural;
   type Stack_Root is abstract tagged private with
     Default_Initial_Condition => Size (Stack_Root) = 0;

   type Model is array (Positive range <>) of Element;

   function Size (S : Stack_Root'Class) return Less_Than_Max;

   function Get_Model (S : Stack_Root) return Model is abstract with
     Ghost,
     Post'Class => Get_Model'Result'First in Less_Than_Max
       and then Get_Model'Result'Last in Less_Than_Max
       and then Get_Model'Result'Length = Size (S);

   function Is_Full (S : Stack_Root'Class) return Boolean is (Size (S) = Max);
   function Is_Empty (S : Stack_Root'Class) return Boolean is (Size (S) = 0);

   procedure Reset (S : in out Stack_Root) is abstract with
     Post'Class => S.Is_Empty;
   function Peek (S : Stack_Root) return Element is abstract with
     Pre'Class  => not S.Is_Empty,
     Post'Class => not S.Is_Empty
       and then Peek'Result = S.Get_Model (S.Get_Model'Last);
   procedure Pop (S : in out Stack_Root; E : out Element) is abstract with
     Pre'Class  => not S.Is_Empty,
     Post'Class => E = S.Peek'Old and
       S.Get_Model = S.Get_Model'Old (S.Get_Model'Old'First ..  S.Get_Model'Old'Last - 1);
   procedure Push (S : in out Stack_Root; E : Element) is abstract with
     Pre'Class  => not S.Is_Full,
     Post'Class => S.Get_Model = S.Get_Model'Old & E;

   type Stack is new Stack_Root with private;

   overriding
   function Get_Model (S : Stack) return Model with
     Ghost;

   overriding
   procedure Reset (S : in out Stack);
   overriding
   function Peek (S : Stack) return Element;
   overriding
   procedure Pop (S : in out Stack; E : out Element);
   overriding
   procedure Push (S : in out Stack; E : Element);

   type Buffer is new Stack_Root with private;

   not overriding
   procedure Enqueue (S : in out Buffer; E : Element) with
     Pre'Class  => not S.Is_Full,
     Post'Class => S.Get_Model = E & S.Get_Model'Old;

   overriding
   function Get_Model (S : Buffer) return Model with
     Ghost;

   overriding
   procedure Reset (S : in out Buffer);
   overriding
   function Peek (S : Buffer) return Element;
   overriding
   procedure Pop (S : in out Buffer; E : out Element);
   overriding
   procedure Push (S : in out Buffer; E : Element);

private
   type Element_Array is array (Positive range 1 .. Max) of Element;
   type Stack_Root is abstract tagged record
      Content : Element_Array := (others => 0);
      Length  : Less_Than_Max := 0;
   end record;
   function Size (S : Stack_Root'Class) return Less_Than_Max is (S.Length);

   type Stack is new Stack_Root with null record;
   function Get_Model (S : Stack) return Model is
     (Model (S.Content (1 .. S.Length)));

   function Peek (S : Stack) return Element is (S.Content (S.Length));

   subtype Positive_Less_Than_Max is Positive range 1 .. Max;

   type Buffer is new Stack with record
      First : Positive_Less_Than_Max := 1;
   end record;

   -- helper functions
   function Wraps_Around (S : Buffer) return Boolean is
     (S.First + S.Length - 1 > Max);
   function Last (S : Buffer) return Less_Than_Max is
     (if not Wraps_Around (S) then S.First + S.Length - 1
      else S.First + S.Length - 1 - Max);

   function Get_Model (S : Buffer) return Model is
     (if Wraps_Around (S) then
           Model (S.Content (S.First .. Max) & S.Content (1 .. Last (S)))
      else Model (S.Content (S.First .. Last (S))));

   function Peek (S : Buffer) return Element is (S.Content (Last (S)));
end Stacks;
