with Flags; use Flags;

procedure Use_Flags (Base : Access_Mode_T)
  with SPARK_Mode
is

   procedure Local (F : Access_Mode_T) with
     Pre =>
       (F and
         (O_Rdonly    or
          O_Wronly    or
          O_Rdwr      or
          O_Exec      or
          O_Accmode   or
          O_Nonblock  or
          O_Append    or
          O_Dsync     or
          O_Rsync     or
          O_Sync      or
          O_Creat     or
          O_Trunc     or
          O_Excl      or
          O_Noctty    or
          O_Nofollow  or
          O_Text      or
          O_Binary    or
          O_Cloexec   or
          O_Realids   or
          O_Largefile or
          O_Async     or
          O_Nosymlink or
          O_Anon      or
          O_Permcheck or
          O_Directory or
          O_Dirfd     )) = F
   is
   begin
      null;
   end;

begin
   Local (Base);
end;
