with Ada.Unchecked_Deallocation;

package body Unbounded_Sequential_Stacks with SPARK_Mode => Off is

   ----------
   -- Push --
   ----------

   procedure Push (Onto : in out Stack;  Item : in Element) is
   begin
      Onto.Head := new Node'(Value => Item, Next => Onto.Head);
      Onto.Count := Onto.Count + 1;
   end Push;

   ----------
   -- Free --
   ----------

   procedure Free is
      new Ada.Unchecked_Deallocation (Object => Node, Name => List);

   ---------
   -- Pop --
   ---------

   procedure Pop (From : in out Stack;  Item : out Element) is
      Temp : List;
   begin
      if From.Count = 0 then
         raise Underflow;
      end if;
      Item := From.Head.Value;
      Temp := From.Head;
      From.Head := From.Head.Next;
      From.Count := From.Count - 1;
      Free (Temp);
   end Pop;

   ---------
   -- Pop --
   ---------

   procedure Pop (This : in out Stack) is
      Temp : List;
   begin
      if This.Count = 0 then
         raise Underflow;
      end if;
      Temp := This.Head;
      This.Head := This.Head.Next;
      This.Count := This.Count - 1;
      Free (Temp);
   end Pop;

   -----------
   -- Depth --
   -----------

   function Depth (This : Stack) return Natural is
   begin
      return This.Count;
   end Depth;

   -----------
   -- Empty --
   -----------

   function Empty (This : Stack) return Boolean is
   begin
      return This.Count = 0;
   end Empty;

   ---------
   -- Top --
   ---------

   function Top (This : Stack) return Reference is
   begin
      return This.Head.Value'Access;
   end Top;

end Unbounded_Sequential_Stacks;
