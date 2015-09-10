---------------------------------------------------------------------------
-- FILE    : postgresql.adb
-- SUBJECT : Body of a simple PostgreSQL interfacing package.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Interfaces.C;
with Interfaces.C.Strings;

use Interfaces.C;
use Interfaces.C.Strings;

package body PostgreSQL is

   type Connection_Status_Type is
     (CONNECTION_OK, CONNECTION_BAD,
      -- Non-blocking mode only below here.
      -- The existence of these should never be relied upon - they should only
      -- be used for user feedback or similar purposes.
      CONNECTION_STARTED,           -- Waiting for connection to be made.
      CONNECTION_MADE,              -- Connection OK; waiting to send.
      CONNECTION_AWAITING_RESPONSE, -- Waiting for a response from the postmaster.
      CONNECTION_AUTH_OK,           -- Received authentication; waiting for backend startup.
      CONNECTION_SETENV,            -- Negotiating environment.
      CONNECTION_SSL_STARTUP,       -- Negotiating SSL.
      CONNECTION_NEEDED)            -- Internal state: connect() needed.
     with Convention => C;

   type Exec_Status_Type is
     (PGRES_EMPTY_QUERY,     -- Empty query was executed.
      PGRES_COMMAND_OK,      -- A query with no expected output was executed successfully.
      PGRES_TUPLES_OK,       -- A query that returns tuples was executed successfully.
      PGRES_COPY_OUT,        -- Copy-out data transfer in progress.
      PGRES_COPY_IN,         -- Copy-in data transfer in progress.
      PGRES_BAD_RESPONSE,    -- The backend produced an unexpected response.
      PGRES_NONFATAL_ERROR,  -- A notice or warning message.
      PGRES_FATAL_ERROR,     -- Query failed.
      PGRES_COPY_BOTH,       -- Copy-in/out data transfer in progress.
      PGRES_SINGLE_TUPLE)    -- A single tuple from a larger result set.
     with Convention => C;

   -- PGconn's true definition is hidden inside libpq. We only need to manipulate pointers
   -- to PGconn objects. However, Ada requires a full declaration for this type so I'm just
   -- using a dummy declaration to satisfy that requirement. TODO: Clean this up!
   --
   type PGconn is new Natural;
   type PGconn_Ptr is access PGconn;

   -- PGresult's true definition is hidden inside libpq. We only need to manipulate pointers...
   type PGresult is new Natural;
   type PGresult_Ptr is access PGresult;

   -- Global data to track the connection and the latest query results.
   Connection_Handle : PGconn_Ptr;
   Connected : Boolean := False;
   Result_Handle : PGresult_Ptr;
   Result_Available : Boolean := False;

   ----------------------
   -- Import Declarations
   ----------------------

   function PQconnectdb(Connection_Info : char_array) return PGConn_Ptr
     with
       Import,
       Convention => C,
       External_Name => "PQconnectdb";

   function PQstatus(Handle : PGconn_Ptr) return Connection_Status_Type
     with
       Import,
       Convention => C,
       External_Name => "PQstatus";

   procedure PQfinish(Handle : in PGconn_Ptr)
     with
       Import,
       Convention => C,
       External_Name => "PQfinish";

   function PQexec(Handle : PGconn_Ptr; Query : char_array) return PGresult_Ptr
     with
       Import,
       Convention => C,
       External_Name => "PQexec";

   function PQresultStatus(Result : PGresult_Ptr) return Exec_Status_Type
     with
       Import,
       Convention => C,
       External_Name => "PQresultStatus";

   procedure PQclear(Result : in PGresult_Ptr)
     with
       Import,
       Convention => C,
       External_Name => "PQclear";

   function PQnfields(Result : PGresult_Ptr) return int
     with
       Import,
       Convention => C,
       External_Name => "PQnfields";

   function PQfname(Result : PGresult_Ptr; Field_Number : int) return chars_ptr
     with
       Import,
       Convention => C,
       External_Name => "PQfname";

   function PQntuples(Result : PGresult_Ptr) return int
     with
       Import,
       Convention => C,
       External_Name => "PQntuples";

   function PQgetvalue
     (Result : PGresult_Ptr; Tuple_Number : int; Field_Number : int) return chars_ptr
     with
       Import,
       Convention => C,
       External_Name => "PQgetvalue";


   ----------------------
   -- Visible Subprograms
   ----------------------


   procedure Connect
     (Server_Name : in String;
      Port        : in Port_Type;
      Database    : in String;
      User        : in String;
      Password    : in String) is

      Connection_String : constant String :=
        "host="      & Server_Name &
        " port="     & Port_Type'Image(Port) &
        " dbname="   & Database &
        " user="     & User &
        " password=" & Password &
        " connect_timeout=15";

   begin
      -- Clean up any active connection.
      Disconnect;

      -- Create a new connection.
      Connection_Handle := PQconnectdb(To_C(Connection_String));
      if PQstatus(Connection_Handle) /= CONNECTION_OK then
         PQfinish(Connection_Handle);
         raise PostgreSQL_Error with "Failed to connect to postmaster";
      end if;
      Connected := True;
   end Connect;


   procedure Disconnect is
   begin
      if Connected then
         Clear_Result;
         PQfinish(Connection_Handle);
         Connected := False;
      end if;
   end Disconnect;


   procedure Execute_Query(Query : in String) is
      Result_Status : Exec_Status_Type;
   begin
      if not Connected then
         raise Not_Connected_Error with "No server connection in Execute_Query";
      end if;

      Clear_Result;

      Result_Handle := PQexec(Connection_Handle, To_C(Query));
      Result_Status := PQresultStatus(Result_Handle);
      if Result_Status = PGRES_COMMAND_OK or Result_Status = PGRES_TUPLES_OK then
         Result_Available := True;
      else
         raise Query_Error with "Query failed during execution";
      end if;
   end Execute_Query;


   procedure Clear_Result is
   begin
      -- TODO: Is it necessary to be connected? If yes, add a raise statement.
      if Result_Available then
         PQclear(Result_Handle);
         Result_Available := False;
      end if;
   end Clear_Result;


   function Number_Of_Fields return Natural is
   begin
      -- TODO: Is it necessary to be connected? If yes, add a raise statement.
      if not Result_Available then
         raise Query_Error with "No query results in Number_Of_Fields";
      end if;
      return Natural(PQnfields(Result_Handle));
   end Number_Of_Fields;


   function Field_Name(Field_Number : Natural) return String is
   begin
      -- TODO: Is it necessary to be connected? If yes, add a raise statement.
      if not Result_Available then
         raise Query_Error with "No query results in Field_Name";
      end if;
      if Field_Number >= Number_Of_Fields then
         raise Query_Error with "Invalid field number in Field_Name";
      end if;
      return Value(PQfname(Result_Handle, int(Field_Number)));
   end Field_Name;


   function Number_Of_Tuples return Natural is
   begin
      -- TODO: Is it necessary to be connected? If yes, add a raise statement.
      if not Result_Available then
         raise Query_Error with "No query results in Number_Of_Tuples";
      end if;
      return Natural(PQntuples(Result_Handle));
   end Number_Of_Tuples;


   function Get_Value(Tuple_Number : Natural; Field_Number : Natural) return String is
   begin
      -- TODO: Is it necessary to be connected? If yes, add a raise statement.
      if not Result_Available then
         raise Query_Error with "No query results in Get_Value";
      end if;
      if Tuple_Number >= Number_Of_Tuples then
         raise Query_Error with "Invalid tuple number in Get_Value";
      end if;
      if Field_Number >= Number_Of_Fields then
         raise Query_Error with "Invalid field number in Get_Value";
      end if;
      return Value(PQgetvalue(Result_Handle, int(Tuple_Number), int(Field_Number)));
   end Get_Value;

end PostgreSQL;
