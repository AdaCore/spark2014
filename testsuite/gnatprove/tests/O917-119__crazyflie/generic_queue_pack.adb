package body Generic_Queue_Pack is

   procedure Enqueue
     (Queue : in out T_Queue;
      Item  : T_Element) is
   begin
      if Queue.Count = Queue.Container'Length then
         return;
      end if;

      Queue.Container (Queue.Rear) := Item;
      Queue.Rear := (if Queue.Rear = Queue.Container'Length then
                        1
                     else
                        Queue.Rear + 1);

      Queue.Count := Queue.Count + 1;
   end Enqueue;

   procedure Dequeue
     (Queue : in out T_Queue;
      Item  : out T_Element) is
   begin
      if Queue.Count = 0 then
         return;
      end if;

      Item := Queue.Container (Queue.Front);
      Queue.Front := (if Queue.Front = Queue.Container'Length then
                         1
                      else
                         Queue.Front + 1);
      Queue.Count := Queue.Count - 1;
   end Dequeue;

   procedure Reset (Queue : in out T_Queue) is
   begin
      Queue.Count := 0;
   end Reset;

   function Is_Empty (Queue : T_Queue) return Boolean is
   begin
      return Queue.Count = 0;
   end Is_Empty;

   function Is_Full (Queue : T_Queue) return Boolean is
   begin
      return Queue.Count = Queue.Container'Length;
   end Is_Full;

      procedure Enqueue_Item
        (Q : in out Protected_Queue;
         Item         : T_Element;
         Has_Succeed  : out Boolean) is
      begin
         if not Is_Full (Q.Queue) then
            Has_Succeed := True;
            Enqueue (Q.Queue, Item);
            Q.Data_Available := True;
         else
            Has_Succeed := False;
         end if;

      end Enqueue_Item;

      procedure Dequeue_Item
        (Q : in out Protected_Queue;
         Item        : out T_Element;
         Has_Succeed : out Boolean) is
      begin
         if not Is_Empty (Q.Queue) then
            Has_Succeed := True;
            Dequeue (Q.Queue, Item);
            Q.Data_Available := not Is_Empty (Q.Queue);
         else
            Has_Succeed := False;
         end if;
      end Dequeue_Item;

      procedure Reset_Queue (Q : in out Protected_Queue) is
      begin
         Reset (Q.Queue);
      end Reset_Queue;

      procedure Await_Item_To_Dequeue
        (Q : in out Protected_Queue; Item : out T_Element) is
      begin
         Dequeue (Q.Queue, Item);
         Q.Data_Available := not Is_Empty (Q.Queue);
      end Await_Item_To_Dequeue;


end Generic_Queue_Pack;
