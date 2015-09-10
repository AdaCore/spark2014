---------------------------------------------------------------------------
-- FILE    : server_spark_boundary.ads
-- SUBJECT : Specification of a package enclosing the SPARK portion of the server.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

with Cryptographic_Services;  -- Contains state (key used).
with Logger;                  -- Boundary variable: Log_Stream.
with Network.Socket.Reader;   -- Boundary variable: Input_Message_Stream.
with Network.Socket.Writer;   -- Boundary variable: Output_Message_Stream.
with Serial_Generator;        -- Contains state (PRNG state).

use Network.Socket;

package Server_SPARK_Boundary is

   procedure Service_Clients
     with
       Global => (Input  => (Reader.Input_Message_Stream, Cryptographic_Services.Key),
                  In_Out =>
                    (Logger.Log_Stream, Writer.Output_Message_Stream, Serial_Generator.State)),
       Depends =>
         (Logger.Log_Stream =>+
            (Reader.Input_Message_Stream, Writer.Output_Message_Stream,
             Cryptographic_Services.Key, Serial_Generator.State),
          Writer.Output_Message_Stream =>+
            (Reader.Input_Message_Stream, Cryptographic_Services.Key, Serial_Generator.State),
          Serial_Generator.State =>+ Reader.Input_Message_Stream);

end Server_SPARK_Boundary;
