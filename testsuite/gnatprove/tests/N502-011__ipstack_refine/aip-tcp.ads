limited with AIP.IP;

package AIP.TCP with
  SPARK_Mode,
  Abstract_State => State
is
   procedure TCP_Input (Buf : Integer; Netif : Integer) with
     Global => (Input  => IP.FIB,
                In_Out => (IP.State, State));

end AIP.TCP;
