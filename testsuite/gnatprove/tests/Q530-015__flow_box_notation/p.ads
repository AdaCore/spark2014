package P is
   type Element is new Integer;

   subtype Stack_Capacity is Positive range Positive'First .. Positive'Last - 1;
   --  the range of values that any given stack object can specify for that
   --  object's physical capacity, ie the number of elements it can possibly
   --  contain

   subtype Stack_Extent is Natural range 0 .. Stack_Capacity'Last;
   --  the number of elements currently contained within any given stack

   type Stack (Capacity : Stack_Capacity) is private;

   function Empty (This : Stack) return Boolean;

   procedure Reset (This : out Stack) with
     Post    => Empty (This),
     Global  => null,
     Depends => (This =>+ null);

private

   type Contents is array (Stack_Capacity range <>) of Element;

   type Stack (Capacity : Stack_Capacity) is record
      Values : Contents (1 .. Capacity);
      Top    : Stack_Extent;
   end record;

end P;
