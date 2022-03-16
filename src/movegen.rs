// SPDX-License-Identifier: GPL-3.0-or-later

use bitboard::*;
use position::Position;
use types::*;

pub const CAPTURES: i32 = 0;
pub const QUIETS: i32 = 1;
pub const QUIET_CHECKS: i32 = 2;
pub const EVASIONS: i32 = 3;
pub const NON_EVASIONS: i32 = 4;
pub const LEGAL: i32 = 5;

pub type GenType = i32;

#[derive(Clone, Copy)]
pub struct ExtMove {
    pub m: Move,
    pub value: i32,
}

// The MoveList struct is a simple wrapper around generate::<*>(). It sometimes
// comes in handy to use this struct instead of the low-level generate::<*>()
// functions.
pub struct MoveList {
    list: [ExtMove; MAX_MOVES],
    idx: usize,
    len: usize,
}

impl MoveList {
    pub fn new<const T: GenType>(pos: &Position) -> MoveList {
        let mut moves = MoveList {
            list: [ExtMove {
                m: Move::NONE,
                value: 0,
            }; MAX_MOVES],
            idx: 0,
            len: 0,
        };
        moves.len = generate::<T>(pos, &mut moves.list, 0);
        moves.idx = 0;
        moves
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn contains(&self, m: Move) -> bool {
        let mut i = 0;
        while i < self.len {
            if self.list[i].m == m {
                return true;
            }
            i += 1;
        }
        return false;
    }
}

impl Iterator for MoveList {
    type Item = Move;
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == self.len {
            None
        } else {
            self.idx += 1;
            Some(self.list[self.idx - 1].m)
        }
    }
}

fn generate_castling<Cr: CastlingRightTrait, const Checks: bool, const Chess960: bool>(
    pos: &Position,
    list: &mut [ExtMove],
    idx: usize,
    us: Color,
) -> usize {
    let king_side = Cr::CR == WHITE_OO || Cr::CR == BLACK_OO;

    if pos.castling_impeded(Cr::CR) || !pos.has_castling_right(Cr::CR) {
        return idx;
    }

    // After castling, the rook and king final positions are the same in
    // Chess960 as they are in standard chess.
    let kfrom = pos.square(us, KING);
    let rfrom = pos.castling_rook_square(Cr::CR);
    let kto = relative_square(us, if king_side { Square::G1 } else { Square::C1 });
    let enemies = pos.pieces_c(!us);

    debug_assert!(pos.checkers() == 0);

    let direction = match Chess960 {
        true => {
            if kto > kfrom {
                WEST
            } else {
                EAST
            }
        }
        false => {
            if king_side {
                WEST
            } else {
                EAST
            }
        }
    };

    let mut s = kto;
    while s != kfrom {
        if pos.attackers_to(s) & enemies != 0 {
            return idx;
        }
        s += direction;
    }

    // Because we generate only legal castling moves, we need to verify that
    // when moving the castling rook we do not discover some hidden checker.
    // For instance an enemy queen on A1 when the castling rook is on B1.
    if Chess960
        && attacks_bb(ROOK, kto, pos.pieces() ^ rfrom) & pos.pieces_cpp(!us, ROOK, QUEEN) != 0
    {
        return idx;
    }

    let m = Move::make_special(CASTLING, kfrom, rfrom);

    if Checks && !pos.gives_check(m) {
        return idx;
    }

    list[idx].m = m;
    idx + 1
}

fn make_promotions<const T: GenType>(
    list: &mut [ExtMove],
    mut idx: usize,
    to: Square,
    ksq: Square,
    direction: Direction,
) -> usize {
    if T == CAPTURES || T == EVASIONS || T == NON_EVASIONS {
        list[idx].m = Move::make_prom(to - direction, to, QUEEN);
        idx += 1;
    }

    if T == QUIETS || T == EVASIONS || T == NON_EVASIONS {
        list[idx].m = Move::make_prom(to - direction, to, ROOK);
        list[idx + 1].m = Move::make_prom(to - direction, to, BISHOP);
        list[idx + 2].m = Move::make_prom(to - direction, to, KNIGHT);
        idx += 3;
    }

    // Knight promotion is the only promotion that can give a direct check
    // that's not already included in the queen promotion.
    if T == QUIET_CHECKS && pseudo_attacks(KNIGHT, to) & ksq != 0 {
        list[idx].m = Move::make_prom(to - direction, to, KNIGHT);
        idx += 1;
    }

    idx
}

// template us
fn generate_pawn_moves<Us: ColorTrait, const T: GenType>(
    pos: &Position,
    list: &mut [ExtMove],
    mut idx: usize,
    target: Bitboard,
) -> usize {
    let us = Us::COLOR;
    let them = !us;
    let trank_8bb = if us == WHITE { RANK8_BB } else { RANK1_BB };
    let trank_7bb = if us == WHITE { RANK7_BB } else { RANK2_BB };
    let trank_3bb = if us == WHITE { RANK3_BB } else { RANK6_BB };
    let up = if us == WHITE { NORTH } else { SOUTH };
    let right = if us == WHITE { NORTH_EAST } else { SOUTH_WEST };
    let left = if us == WHITE { NORTH_WEST } else { SOUTH_EAST };

    let mut empty_squares = Bitboard(0);

    let pawns_on_7 = pos.pieces_cp(us, PAWN) & trank_7bb;
    let pawns_not_on_7 = pos.pieces_cp(us, PAWN) & !trank_7bb;

    let enemies = match T {
        EVASIONS => pos.pieces_c(them) & target,
        CAPTURES => target,
        _ => pos.pieces_c(them),
    };

    // Single and double pawn pushes, no promotions
    if T != CAPTURES {
        empty_squares = if T == QUIETS || T == QUIET_CHECKS {
            target
        } else {
            !pos.pieces()
        };

        let mut b1 = pawns_not_on_7.shift(up) & empty_squares;
        let mut b2 = (b1 & trank_3bb).shift(up) & empty_squares;

        if T == EVASIONS {
            // Consider only blocking squares
            b1 &= target;
            b2 &= target;
        }

        if T == QUIET_CHECKS {
            let ksq = pos.square(them, KING);

            b1 &= pos.attacks_from_pawn(ksq, them);
            b2 &= pos.attacks_from_pawn(ksq, them);

            // Add pawn pushes which give discovered check. This is possible
            // only if the pawn is not on the same file as the enemy king,
            // because we don't generate captures. Note that a possible
            // discovery check promotion has already been generated together
            // with the captures.
            let dc_candidates = pos.blockers_for_king(them);
            if pawns_not_on_7 & dc_candidates != 0 {
                let dc1 = (pawns_not_on_7 & dc_candidates).shift(up)
                    & empty_squares
                    & !file_bb(ksq.file());
                let dc2 = (dc1 & trank_3bb).shift(up) & empty_squares;

                b1 |= dc1;
                b2 |= dc2;
            }
        }

        for to in b1 {
            list[idx].m = Move::make(to - up, to);
            idx += 1;
        }

        for to in b2 {
            list[idx].m = Move::make(to - up - up, to);
            idx += 1;
        }
    }

    // Promotions and underpromotions
    if pawns_on_7 != 0 && (T != EVASIONS || target & trank_8bb != 0) {
        if T == CAPTURES {
            empty_squares = !pos.pieces();
        }

        if T == EVASIONS {
            empty_squares &= target;
        }

        let b1 = pawns_on_7.shift(right) & enemies;
        let b2 = pawns_on_7.shift(left) & enemies;
        let b3 = pawns_on_7.shift(up) & empty_squares;

        let ksq = pos.square(them, KING);

        for s in b1 {
            idx = make_promotions::<T>(list, idx, s, ksq, right);
        }

        for s in b2 {
            idx = make_promotions::<T>(list, idx, s, ksq, left);
        }

        for s in b3 {
            idx = make_promotions::<T>(list, idx, s, ksq, up);
        }
    }

    // Standard and en-passant captures
    if T == CAPTURES || T == EVASIONS || T == NON_EVASIONS {
        let b1 = pawns_not_on_7.shift(right) & enemies;
        let b2 = pawns_not_on_7.shift(left) & enemies;

        for to in b1 {
            list[idx].m = Move::make(to - right, to);
            idx += 1;
        }

        for to in b2 {
            list[idx].m = Move::make(to - left, to);
            idx += 1;
        }

        if pos.ep_square() != Square::NONE {
            debug_assert!(pos.ep_square().rank() == relative_rank(us, RANK_6));

            // An en passant capture can be an evasion only if the checking
            // piece is the double pushed pawn and so is in the target.
            // Otherwise this is a discovery check and we are forced to do
            // otherwise.
            if T == EVASIONS && target & (pos.ep_square() - up) == 0 {
                return idx;
            }

            let b1 = pawns_not_on_7 & pos.attacks_from_pawn(pos.ep_square(), them);

            debug_assert!(b1 != 0);

            for to in b1 {
                list[idx].m = Move::make_special(ENPASSANT, to, pos.ep_square());
                idx += 1;
            }
        }
    }

    idx
}

fn generate_moves<const Pt: PieceType, const Checks: bool>(
    pos: &Position,
    list: &mut [ExtMove],
    mut idx: usize,
    us: Color,
    target: Bitboard,
) -> usize {
    debug_assert!(Pt != KING && Pt != PAWN);

    for from in pos.square_list(us, Pt) {
        if Checks {
            if (Pt == BISHOP || Pt == ROOK || Pt == QUEEN)
                && pseudo_attacks(Pt, from) & target & pos.check_squares(Pt) == 0
            {
                continue;
            }

            if pos.blockers_for_king(!us) & from != 0 {
                continue;
            }
        }

        let mut b = pos.attacks_from(Pt, from) & target;

        if Checks {
            b &= pos.check_squares(Pt);
        }

        for to in b {
            list[idx].m = Move::make(from, to);
            idx += 1;
        }
    }

    idx
}

fn generate_all<Us: ColorTrait, const T: GenType, const Checks: bool>(
    pos: &Position,
    list: &mut [ExtMove],
    mut idx: usize,
    target: Bitboard,
) -> usize {
    let us = Us::COLOR;

    idx = generate_pawn_moves::<Us, T>(pos, list, idx, target);
    idx = generate_moves::<KNIGHT, Checks>(pos, list, idx, us, target);
    idx = generate_moves::<BISHOP, Checks>(pos, list, idx, us, target);
    idx = generate_moves::<ROOK, Checks>(pos, list, idx, us, target);
    idx = generate_moves::<QUEEN, Checks>(pos, list, idx, us, target);

    if T != QUIET_CHECKS && T != EVASIONS {
        let ksq = pos.square(us, KING);
        let b = pos.attacks_from(KING, ksq) & target;
        for to in b {
            list[idx].m = Move::make(ksq, to);
            idx += 1;
        }
    }

    if T != CAPTURES && T != EVASIONS && pos.can_castle(us) {
        if pos.is_chess960() {
            idx = generate_castling::<Us::KingSide, Checks, true>(pos, list, idx, us);
            idx = generate_castling::<Us::QueenSide, Checks, true>(pos, list, idx, us);
        } else {
            idx = generate_castling::<Us::KingSide, Checks, false>(pos, list, idx, us);
            idx = generate_castling::<Us::QueenSide, Checks, false>(pos, list, idx, us);
        }
    }

    idx
}

// generate_quiet_checks() generates all pseudo-legal non-captures and
// knight underpromotions that give check
pub fn generate_quiet_checks(pos: &Position, list: &mut [ExtMove], mut idx: usize) -> usize {
    debug_assert!(pos.checkers() == 0);

    let us = pos.side_to_move();
    let dc = pos.blockers_for_king(!us) & pos.pieces_c(us);

    for from in dc {
        let pt = pos.piece_on(from).piece_type();

        if pt == PAWN {
            continue; // Will be generated together with direct checks
        }

        let mut b = pos.attacks_from(pt, from) & !pos.pieces();

        if pt == KING {
            b &= !pseudo_attacks(QUEEN, pos.square(!us, KING));
        }

        for to in b {
            list[idx].m = Move::make(from, to);
            idx += 1;
        }
    }

    if us == WHITE {
        generate_all::<White, QUIET_CHECKS, true>(pos, list, idx, !pos.pieces())
    } else {
        generate_all::<Black, QUIET_CHECKS, true>(pos, list, idx, !pos.pieces())
    }
}

// generate_evasions() generates all pseudo-legal check evasions when the
// side to move is in check
fn generate_evasions(pos: &Position, list: &mut [ExtMove], mut idx: usize) -> usize {
    debug_assert!(pos.checkers() != 0);

    let us = pos.side_to_move();
    let ksq = pos.square(us, KING);
    let mut slider_attacks = Bitboard(0);
    let sliders = pos.checkers() & !pos.pieces_pp(KNIGHT, PAWN);

    // Find all the squares attacked by slider checks. We will remove them
    // from the king evasions in order to skip known illegal moves, which
    // avoids any useless legality checks later on.
    for check_sq in sliders {
        slider_attacks |= line_bb(check_sq, ksq) ^ check_sq;
    }

    // Generate evasions for king, capture and non-capture moves
    let b = pos.attacks_from(KING, ksq) & !pos.pieces_c(us) & !slider_attacks;
    for to in b {
        list[idx].m = Move::make(ksq, to);
        idx += 1;
    }

    if more_than_one(pos.checkers()) {
        return idx; // Double check, only a king move can save the day
    }

    // Generate blocking evasions or captures of the checking piece
    let check_sq = lsb(pos.checkers());
    let target = between_bb(check_sq, ksq) | check_sq;

    if us == WHITE {
        generate_all::<White, EVASIONS, false>(pos, list, idx, target)
    } else {
        generate_all::<Black, EVASIONS, false>(pos, list, idx, target)
    }
}

// generate_legal() generates all the legal moves in the given position
fn generate_legal(pos: &Position, list: &mut [ExtMove], idx: usize) -> usize {
    let us = pos.side_to_move();
    let pinned = pos.blockers_for_king(us) & pos.pieces_c(us);
    let ksq = pos.square(us, KING);

    let pseudo = if pos.checkers() != 0 {
        generate::<EVASIONS>(pos, list, idx)
    } else {
        generate::<NON_EVASIONS>(pos, list, idx)
    };

    let mut legal = idx;
    for i in idx..pseudo {
        let m = list[i].m;
        if (pinned == 0 && m.from() != ksq && m.move_type() != ENPASSANT) || pos.legal(m) {
            list[legal].m = m;
            legal += 1;
        }
    }

    legal
}

// generate<Captures>() generates all pseudo-legal captures and queen
// promotions.
//
// generate<Quiets>() generates all pseudo-legal non-captures and
// underpromotions.
//
// generate<QuietChecks>() generates all pseudo-legal non-captures and
// knight underpromotions that give check.
//
// generate<Evasions>() generates all pseudo-legal check evasions when the
// side to move is in check.
//
// generate<NonEvasions>() generates all pseudo-legal captures and
// non-captures.
//
// generate<Legal>() generates all the legal moves in the given position.

pub fn generate<const T: GenType>(pos: &Position, list: &mut [ExtMove], idx: usize) -> usize {
    match T {
        QUIET_CHECKS => generate_quiet_checks(pos, list, idx),
        EVASIONS => generate_evasions(pos, list, idx),
        LEGAL => generate_legal(pos, list, idx),
        _ => {
            debug_assert!(pos.checkers() == 0);

            let us = pos.side_to_move();

            let target = match T {
                CAPTURES => pos.pieces_c(!us),
                QUIETS => !pos.pieces(),
                NON_EVASIONS => !pos.pieces_c(us),
                _ => Bitboard(0),
            };

            if us == WHITE {
                generate_all::<White, T, false>(pos, list, idx, target)
            } else {
                generate_all::<Black, T, false>(pos, list, idx, target)
            }
        }
    }
}
