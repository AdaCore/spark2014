with Types; use Types;

package Stacks
  with SPARK_Mode
is

   type Stack is private;

   Empty_Stack : constant Stack;

   function Is_Empty (S : Stack) return Boolean;
   function Is_Full (S : Stack) return Boolean;
   function Size (S : Stack) return Index;

   procedure Push (S : in out Stack; E : Element)
   with
     Pre => not S.Is_Full,
     Post => S.Size = S.Size'Old + 1;

   function Pop (S : in out Stack) return Element
   with
     Side_Effects,
     Pre => not S.Is_Empty,
     Post => S.Size = S.Size'Old - 1;

private

   type Content_Table is new Table (1 .. 20) with Relaxed_Initialization;

   type Stack is record
      Top     : Index;
      Content : Content_Table;
   end record
     with Ghost_Predicate => Top in 0 .. 20
       and then Content (1 .. Top)'Initialized;

   Empty_Stack : constant Stack := (Top => 0, Content => (others => <>));

   function Is_Empty (S : Stack) return Boolean is (S.Top = 0);
   function Is_Full (S : Stack) return Boolean is (S.Top = 20);
   function Size (S : Stack) return Index is (S.Top);

end Stacks;
