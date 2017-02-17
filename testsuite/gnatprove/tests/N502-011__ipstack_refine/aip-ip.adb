with AIP.UDP;
with AIP.TCP;

package body AIP.IP with
  SPARK_Mode,
  Refined_State => (State => IP_Serial,
                    FIB   => Default_Router)
is
   Default_Router : Integer := 0;
   IP_Serial : Integer := 0;

   procedure IP_Input (Netif : Integer; Buf : Integer) with
     Refined_Global => (Input  => (Default_Router, UDP.State),
                        In_Out => (IP_Serial, TCP.State))
   is
   begin
      null;
   end IP_Input;

end AIP.IP;
