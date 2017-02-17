limited with AIP.UDP;
limited with AIP.TCP;

package AIP.IP with
  SPARK_Mode,
  Abstract_State => (FIB, State),
  Initializes    => (FIB, State)
is
   procedure IP_Input (Netif : Integer; Buf : Integer) with
     Global => (Input  => (FIB, UDP.State),
                In_Out => (TCP.State, State));
   pragma Export (C, IP_Input, "AIP_ip_input");

end AIP.IP;
