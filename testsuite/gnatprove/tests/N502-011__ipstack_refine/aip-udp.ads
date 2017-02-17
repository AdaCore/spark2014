with AIP.IP;

package AIP.UDP with
  SPARK_Mode,
  Abstract_State => State
is
   procedure UDP_Input (Buf : Integer; Netif : Integer) with
     Global => (Input => State);

end AIP.UDP;
