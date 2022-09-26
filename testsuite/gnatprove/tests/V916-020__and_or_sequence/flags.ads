with Interfaces;

package Flags
  with SPARK_Mode
is
   type Access_Mode_T is private;
   function "and"
     (L, R : Access_Mode_T)
      return Access_Mode_T with
      Inline;
   function "or"
     (L, R : Access_Mode_T)
      return Access_Mode_T with
      Inline;

   O_Rdonly    : constant Access_Mode_T;
   O_Wronly    : constant Access_Mode_T;
   O_Rdwr      : constant Access_Mode_T;
   O_Exec      : constant Access_Mode_T;
   O_Accmode   : constant Access_Mode_T;
   O_Nonblock  : constant Access_Mode_T;
   O_Append    : constant Access_Mode_T;
   O_Dsync     : constant Access_Mode_T;
   O_Rsync     : constant Access_Mode_T;
   O_Sync      : constant Access_Mode_T;
   O_Creat     : constant Access_Mode_T;
   O_Trunc     : constant Access_Mode_T;
   O_Excl      : constant Access_Mode_T;
   O_Noctty    : constant Access_Mode_T;
   O_Nofollow  : constant Access_Mode_T;
   O_Text      : constant Access_Mode_T;
   O_Binary    : constant Access_Mode_T;
   O_Cloexec   : constant Access_Mode_T;
   O_Realids   : constant Access_Mode_T;
   O_Largefile : constant Access_Mode_T;
   O_Async     : constant Access_Mode_T;
   O_Nosymlink : constant Access_Mode_T;
   O_Anon      : constant Access_Mode_T;
   O_Permcheck : constant Access_Mode_T;
   O_Directory : constant Access_Mode_T;
   O_Dirfd     : constant Access_Mode_T;

private

   type Access_Mode_T is new Interfaces.Unsigned_32;
   O_Rdonly    : constant Access_Mode_T := 0;
   O_Wronly    : constant Access_Mode_T := 2**0;
   O_Rdwr      : constant Access_Mode_T := 2**1;
   O_Exec      : constant Access_Mode_T := 2**2;
   O_Accmode   : constant Access_Mode_T := 2**3;
   O_Nonblock  : constant Access_Mode_T := 2**4;
   O_Append    : constant Access_Mode_T := 2**5;
   O_Dsync     : constant Access_Mode_T := 2**6;
   O_Rsync     : constant Access_Mode_T := 2**7;
   O_Sync      : constant Access_Mode_T := 2**8;
   O_Creat     : constant Access_Mode_T := 2**9;
   O_Trunc     : constant Access_Mode_T := 2**10;
   O_Excl      : constant Access_Mode_T := 2**11;
   O_Noctty    : constant Access_Mode_T := 2**12;
   O_Nofollow  : constant Access_Mode_T := 2**13;
   O_Text      : constant Access_Mode_T := 2**14;
   O_Binary    : constant Access_Mode_T := 2**15;
   O_Cloexec   : constant Access_Mode_T := 2**16;
   O_Realids   : constant Access_Mode_T := 2**17;
   O_Largefile : constant Access_Mode_T := 2**18;
   O_Async     : constant Access_Mode_T := 2**19;
   O_Nosymlink : constant Access_Mode_T := 2**20;
   O_Anon      : constant Access_Mode_T := 2**21;
   O_Permcheck : constant Access_Mode_T := 2**22;
   O_Directory : constant Access_Mode_T := 2**23;
   O_Dirfd     : constant Access_Mode_T := 2**24;

   use Interfaces;

   function "and"
     (L, R : Access_Mode_T)
      return Access_Mode_T is
     (Access_Mode_T (Unsigned_32 (L) and Unsigned_32 (R)));
   function "or"
     (L, R : Access_Mode_T)
      return Access_Mode_T is
     (Access_Mode_T (Unsigned_32 (L) or Unsigned_32 (R)));

end Flags;
