generic
   type Element is private;
   Default_Element : Element;
package Bounded_Stacks is

   type Stack (Capacity : Positive) is tagged private
      with Default_Initial_Condition => Empty (Stack);

   function "=" (Left, Right : Stack) return Boolean;

   function Extent (This : Stack) return Natural;

   function Empty (This : Stack) return Boolean;

   function Full (This : Stack) return Boolean;

   procedure Reset (This : out Stack) with
     Post'Class => Empty (This) and
                   not Full (This),
     Global     => null,
     Depends    => (This =>+ null),
     Annotate   => (GNATprove,
                    Intentional,
                    """This.Values"" is not set",
                    "Because zeroing Top is sufficient");

   procedure Push (This : in out Stack;  Item : Element) with
     Pre'Class  => not Full (This) and
                   Extent (This) < This.Capacity,
     Post'Class => not Empty (This) and
                   Extent (This) = Extent (This'Old) + 1,
     Global     => null,
     Depends    => (This =>+ Item);

   procedure Pop (This : in out Stack;  Item : out Element) with
     Pre'Class  => not Empty (This),
     Post'Class => not Full (This) and
                   Extent (This) = Extent (This'Old) - 1,
     Global     => null,
     Depends    => (This =>+ null, Item => This);

   function Peek (This : Stack) return Element with
     Pre'Class => not Empty (This),
     Global    => null,
     Depends   => (Peek'Result => This);

private

   type Contents is array (Positive range <>) of Element;

   type Stack (Capacity : Positive) is tagged record
      Values : Contents (1 .. Capacity); -- := (others => Default_Element);
--        Top    : Natural;
      Top    : Natural := 0;
   end record with Predicate => Top <= Capacity,
     Annotate => (GNATprove,
                  Intentional,
                  "type ""Stack"" is not fully initialized",
                  "Because zeroing Top is sufficient");

end Bounded_Stacks;
