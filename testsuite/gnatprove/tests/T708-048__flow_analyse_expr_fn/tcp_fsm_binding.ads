with Tcp_Type;       use Tcp_Type;
package Tcp_Fsm_Binding
   with SPARK_Mode
is
   procedure Tcp_Process_One_Segment (Sock : in out Not_Null_Socket)
   with
      Global => null,
      Post   => Tcp_Syn_Queue_Item_Model(Sock.synQueue);
end Tcp_Fsm_Binding;
