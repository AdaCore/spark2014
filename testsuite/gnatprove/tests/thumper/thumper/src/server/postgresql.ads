---------------------------------------------------------------------------
-- FILE    : postgresql.ads
-- SUBJECT : Specification of a simple PostgreSQL interfacing package.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------

-- Package that manages a single connection to a PostgreSQL server.
-- NOTE: This package is not task-safe; it assumes only a single task accesses it at a time.
package PostgreSQL is

   type Port_Type is range 0 .. 65535;

   Not_Connected_Error : exception;
   PostgreSQL_Error : exception;
   Query_Error : exception;

   -- Only a single connection at a time is supported. It is permitted to call Connect if a
   -- connection is already active. In that case the current connection is closed first. Most
   -- of the subprograms in this package propagate Not_Connected_Error if no connection is
   -- active. An exception to that rule is the Disconnect procedure.
   --
   -- PostgreSQL_Error is propagated if the connection can't be made.
   procedure Connect
     (Server_Name : in String;
      Port        : in Port_Type;
      Database    : in String;
      User        : in String;
      Password    : in String);

   -- Disconnects from the server. If called without an active connection, there is no effect.
   -- If there are query results available they are cleared.
   procedure Disconnect;

   -- Executes the query (in general an SQL query, but could also be a PostgreSQL command).
   -- Only a single query can be active at a time. If a previous query returned results, those
   -- results are discarded before this query is attempted. When the results of a query are no
   -- longer needed Clear_Result should be called.
   --
   -- Not_Connected_Error is propagated if there is no active connection.
   procedure Execute_Query(Query : in String);

   -- Removes the results of the previous query, if any.
   procedure Clear_Result;

   -- Returns the number of fields in the available query result.
   -- Query_Error is propagated if there is no result.
   function Number_Of_Fields return Natural;

   -- Returns the name of the specified field.
   -- Query_Error is propagated if there is no result or if the field number is invalid.
   function Field_Name(Field_Number : Natural) return String;

   -- Returns the number of tuples in the available query result.
   -- Query_Error is propagated if there is no result.
   function Number_Of_Tuples return Natural;

   -- Returns the value of the indicated field in the indicated tuple.
   -- Query_Error is propagated if there is no result or if a given number is invalid.
   function Get_Value(Tuple_Number : Natural; Field_Number : Natural) return String;

end PostgreSQL;
