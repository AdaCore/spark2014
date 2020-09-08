package Tcp_Type is
   type Tcp_Syn_Queue_Item;
   type Tcp_Syn_Queue_Item_Acc is access Tcp_Syn_Queue_Item;
   type Tcp_Syn_Queue_Item is
    record
      Next : Tcp_Syn_Queue_Item_Acc;
    end record;

   type Socket_Struct is record
      synQueue : Tcp_Syn_Queue_Item_Acc;
   end record;
   type Socket is access Socket_Struct;
   subtype Not_Null_Socket is not null Socket;

   function Tcp_Syn_Queue_Item_Model
      (Queue : access constant Tcp_Syn_Queue_Item) return Boolean is
      (Queue = null or else
         (Tcp_Syn_Queue_Item_Model (Queue.Next)))
      with Ghost;
end Tcp_Type;
