--=head1 NAME
--
--  Clock - interface to the system clock
--
--=head1 REVISION HISTORY
--
-- $Log: clock.ads,v $
-- Revision 1.2  2004/08/09 17:07:55  adi
-- Added POD commands to clock.ads
--
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
-- Revision 1.3  2003/09/01 18:17:34  adi
-- Added base type assertion for clock
--
-- Revision 1.2  2003/02/13 00:10:25  adi
-- Added Command point
--
-- Revision 1.1  2003/02/08 17:38:40  adi
-- Initial revision
--
--=cut
package Clock
  --# own Time;
  --# initializes Time;
is
   --=head1 TYPES
   --
   --=over 4
   --
   --=cut

   --=item *
   --
   type Millisecond is range 0..(100*(3600*24));
   --
   --Number of milliseconds, measured over 1 day
   --
   --=cut

   --# assert millisecond'base is long_integer;

   --
   --=back
   --
   --=head1 SUBPROGRAMS
   --
   --=over 4

   --=item *
   --
   procedure Read(T : out Millisecond;
                  Valid : out Boolean);
   --# global in out Time;
   --# derives T, Valid, Time from Time;
   --
   --Read the current time.  If the time is not valid,
   --C<Valid> will be false and C<T> will be an arbitrary value.
   --

   --=item *
   --
   function Time_Valid return Boolean;
   --# global in Time;
   --
   --Check whether the current clock value is known to be valid
   --

   --=item *
   --
   procedure Reset;
   --# global out Time;
   --# derives Time from;
   --
   --Reset the clock
   --

   --=item *
   --
   procedure Cycle(Plus : in Millisecond);
   --# global in out Time;
   --# derives Time from *, Plus;
   --
   --Interface for simulation; allow control of the clock, cycling
   --forward exactly C<Plus> milliseconds.
   --

   --=item *
   --
   procedure Command;
   --# derives;
   --
   --Test harness point.  Reads controlling keywords from
   --standard input, and adjusts clock state accordingly.
   --

   --=back
   --
   --=cut
end Clock;

--=head1 NOTES
--
--This package pretends to be a system clock.  Regular code can
--read and reset the clock time and validity.  The extra interfaces
--permit precise simulator control over the clock's behaviour.  The
--clock reading will wrap around to 0 milliseconds at the end of one
--entire day.
--
--=cut
