with Interfaces;
with Interfaces.C; use Interfaces.C;
with System;

procedure Neutrino
  with SPARK_Mode
is

   type Zero_8_T is new Interfaces.Integer_8 range 0 .. 0 with
      Default_Value => 0;
   type Array_Of_Zero_8_T is array (Natural range <>) of Zero_8_T;

   Pulse_Type    : constant := 0;

   type Sival_Int_T is new Interfaces.Integer_32;

   type Sigval_Kind_T is (Number, Address);
   type Sigval_T (Kind : Sigval_Kind_T := Number) is record
      case Kind is
         when Number =>
            Sival_Int : Sival_Int_T;
         when Address =>
            Sival_Ptr : System.Address;
      end case;
   end record;
   pragma Convention (C, Sigval_T);
   pragma Unchecked_Union (Sigval_T);

   type Connection_Id_T is range -1 .. Interfaces.C.int'last with
      Size => Interfaces.C.int'size;

   type Pulse_T is record
      The_Type    : Interfaces.Unsigned_16 := Pulse_Type;
      The_Subtype : Interfaces.Unsigned_16 := Pulse_Type;
      Code        : Interfaces.Integer_8;
      Zero        : Array_Of_Zero_8_T (0 .. 2);
      Value       : Sigval_T;
      Scoid       : Connection_Id_T;
   end record with
      Convention => C;

   type Errno_T is
     (Eok, Eperm, Enoent, Esrch, Eintr, Eio, Enxio, E2big, Enoexec, Ebadf,
      Echild, Eagain, Enomem, Eacces, Efault, Enotblk, Ebusy, Eexist, Exdev,
      Enodev, Enotdir, Eisdir, Einval, Enfile, Emfile, Enotty, Etxtbsy, Efbig,
      Enospc, Espipe, Erofs, Emlink, Epipe, Edom, Erange, Enomsg, Eidrm,
      Echrng, El2nsync, El3hlt, El3rst, Elnrng, Eunatch, Enocsi, El2hlt,
      Edeadlk, Enolck, Ecanceled, Enotsup, Edquot, Ebade, Ebadr, Exfull,
      Enoano, Ebadrqc, Ebadslt, Edeadlock, Ebfont, Eownerdead, Enostr, Enodata,
      Etime, Enosr, Enonet, Enopkg, Eremote, Enolink, Eadv, Esrmnt, Ecomm,
      Eproto, Emultihop, Ebadmsg, Enametoolong, Eoverflow, Enotuniq, Ebadfd,
      Eremchg, Elibacc, Elibbad, Elibscn, Elibmax, Elibexec, Eilseq, Enosys,
      Eloop, Erestart, Estrpipe, Enotempty, Eusers, Enotrecoverable,
      Eopnotsupp, Efpos, Estale, Einprogress, Ealready, Enotsock, Edestaddrreq,
      Emsgsize, Eprototype, Enoprotoopt, Eprotonosupport, Esocktnosupport,
      Epfnosupport, Eafnosupport, Eaddrinuse, Eaddrnotavail, Enetdown,
      Enetunreach, Enetreset, Econnaborted, Econnreset, Enobufs, Eisconn,
      Enotconn, Eshutdown, Etoomanyrefs, Etimedout, Econnrefused, Ehostdown,
      Ehostunreach, Ebadrpc, Erpcmismatch, Eprogunavail, Eprogmismatch,
      Eprocunavail, Enoremote, Enondp, Ebadfsys, Emore, Ectrlterm, Enolic,
      Esrvrfault, Eendian, Esectypeinval) with
      Size => Interfaces.C.int'size;

   type Msg_Info64_T is record
      Nd        : Integer;
   end record;
   --  Pragma used because record includes types that are
   --  not yet fully defined
   pragma Convention (C, Msg_Info64_T);

   subtype Msg_Info_T is Msg_Info64_T;

   type Channel_Id_T is
     new Interfaces.C.int range -1 .. Interfaces.C.int'last with
      Size => Interfaces.C.int'size;

   procedure Msg_Receive_Pulse_R
     (Pulse  : out Pulse_T;
      Bytes  :     Size_T;
      Info   :     access Msg_Info_T := null;
      Status : out Errno_T)
   with
      Inline,
      Global => null,
      Relaxed_Initialization => Pulse,
      Post =>
        (Status in Efault | Eintr | Esrch | Etimedout)
          or else
        (Status = Eok and then
         True); --  Pulse'Initialized is not allowed for unchecked union

   procedure Msg_Receive_Pulse_R
     (Pulse  : out Pulse_T;
      Bytes  :     Size_T;
      Info   :     access Msg_Info_T := null;
      Status : out Errno_T)
   with SPARK_Mode => Off
   is
   begin
      Status := Efault;
   end;

   Status : Errno_T;
begin
   for Runs in 1 .. 100 loop
      -- receive pulse
      declare
         Pulse : Pulse_T;
      begin
         Msg_Receive_Pulse_R
           (Pulse  => Pulse,  -- @INIT_BY_PROOF:FAIL
            Bytes  => 0,
            Status => Status);

         if Status /= Eok then
            -- handle error
            null;

         else
            -- handle pulse
            declare
               Scoid : constant Connection_Id_T := Pulse.Scoid;
            begin
               null;
            end;
         end if;
      end;
   end loop;

   pragma Assert (Status = Eok);
end;
