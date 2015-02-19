package StackP with SPARK_Mode is
   Max : constant Natural := 100;
   subtype Less_Than_Max is Natural range 0 .. Max;

   type Element is new Natural;
   type Stack_Root is abstract tagged private with
     Default_Initial_Condition => Size (Stack_Root) = 0;

   type Model is array (Positive range <>) of Element;

   function Size (S : Stack_Root'Class) return Less_Than_Max;
   function Get_Model (S : Stack_Root) return Model is abstract with
     Post'Class => Get_Model'Result'Length = Size (S);

   function Is_Full (S : Stack_Root'Class) return Boolean is (Size (S) = Max);
   function Is_Empty (S : Stack_Root'Class) return Boolean is (Size (S) = 0);

   procedure Reset (S : out Stack_Root) is abstract with
     Post'Class => Is_Empty (S);
   procedure Pop (S : in out Stack_Root; E : out Element) is abstract with
     Pre'Class  => not Is_Empty (S),
     Post'Class => Get_Model (S) & (1 => E) = Get_Model (S)'Old;
   procedure Push (S : in out Stack_Root; E : Element) is abstract with
     Pre'Class  => not Is_Full (S),
     Post'Class => Get_Model (S) = Get_Model (S)'Old & (1 => E);

   type Stack is new Stack_Root with private;

   -- Proofs don't go through without restating Post'Class everywhere.
   -- Ideally, we would like to remove the redundant ones.

   overriding
   function Get_Model (S : Stack) return Model;

   overriding
   procedure Reset (S : out Stack);
   overriding
   procedure Pop (S : in out Stack; E : out Element) with
     Post'Class => Get_Model (S) & (1 => E) = Get_Model (S)'Old;
   overriding
   procedure Push (S : in out Stack; E : Element) with
     Post'Class => Get_Model (S) = Get_Model (S)'Old & (1 => E);

   type Buffer is new Stack_Root with private;

   not overriding
   procedure Enqueue (S : in out Buffer; E : Element) with
     Pre'Class  => not Is_Full (S),
     Post'Class => Get_Model (S) = E & Get_Model (S)'Old;

   overriding
   function Get_Model (S : Buffer) return Model;

   overriding
   procedure Reset (S : out Buffer);
   overriding
   procedure Pop (S : in out Buffer; E : out Element) with
     Post'Class => Get_Model (S) & (1 => E) = Get_Model (S)'Old;
   overriding
   procedure Push (S : in out Buffer; E : Element) with
     Post'Class => Get_Model (S) = Get_Model (S)'Old & (1 => E);

private
   type Element_Array is array (Positive range 1 .. Max) of Element;
   type Stack_Root is abstract tagged record
      Content : Element_Array;
      Length  : Less_Than_Max := 0;
   end record;
   function Size (S : Stack_Root'Class) return Less_Than_Max is (S.Length);

   type Stack is new Stack_Root with null record;
   function Get_Model (S : Stack) return Model is
     (Model (S.Content (1 .. S.Length)));

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
end StackP;
