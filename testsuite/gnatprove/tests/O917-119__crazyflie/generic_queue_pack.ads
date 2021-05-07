with System;

generic
   type T_Element is private;
   Def : T_Element;

package Generic_Queue_Pack is

   --  Types

   type T_Queue (Length : Positive) is private with Default_Initial_Condition;

   --  Procedures and functions

   --  Enqueue an item in the queue, if the queue is not full.
   procedure Enqueue
     (Queue : in out T_Queue;
      Item  : T_Element);

   --  Dequeue an item from the queue, if the queue is not empty.
   procedure Dequeue
     (Queue : in out T_Queue;
      Item  : out T_Element);

   --  Reset the queue by setting the count to 0.
   procedure Reset (Queue : in out T_Queue);

   --  Return True if the queue is empty, False otherwise.
   function Is_Empty (Queue : T_Queue) return Boolean;

   --  Return True if the queue is full, False otherwise.
   function Is_Full (Queue : T_Queue) return Boolean;

   --  Tasks and protected types

   --  Protected type used to access a queue that can be
   --  used by various tasks.
   type Protected_Queue
     (Ceiling    : System.Any_Priority;
      Queue_Size : Positive) is record
      Data_Available : Boolean := False;
      Queue          : T_Queue (Queue_Size);

   end record;

      procedure Enqueue_Item
        (Q : in out Protected_Queue;
         Item         : T_Element;
         Has_Succeed  : out Boolean);

      procedure Dequeue_Item
        (Q : in out Protected_Queue;
         Item        : out T_Element;
         Has_Succeed : out Boolean);

      procedure Reset_Queue (Q : in out Protected_Queue);

      procedure Await_Item_To_Dequeue (Q : in out Protected_Queue; Item : out T_Element);


private

   --  Types

   --  Type for arrays containing T_Element type items,
   --  T_Element type given as generic parameter.
   type Element_Array is array (Positive range <>) of T_Element;

   --  Type representing a generic queue.
   type T_Queue (Length : Positive) is record
      Container : Element_Array (1 .. Length) := (others => Def);
      Count     : Natural := 0;
      Front     : Positive := 1;
      Rear      : Positive := 1;
   end record;

end Generic_Queue_Pack;
