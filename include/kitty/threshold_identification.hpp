/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author Canberk Sönmez
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h>
#include "traits.hpp"
#include "properties.hpp"
#include "isop.hpp"

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  auto nvars = tt.num_vars();
  auto fstar = tt;
  std::vector<int64_t> linear_form(nvars + 1, 0);
  std::vector<bool> negated(nvars, false);

  // Step 1 - Check if the given function is unate in all of its variables
  for ( auto i = 0u; i < nvars; ++i )
  {
    switch ( get_unateness( tt, i ) )
    {
    case unateness::binate:
      return false;
    case unateness::negative:
      flip_inplace(fstar, i);
      negated[i] = true;
      break;
    default:
      break;
    }
  }

  // to speed up the ILP part, we can work on the irredundant SOP
  // representations
  std::vector<cube> fstarcubes = isop(fstar);
  std::vector<cube> fstarnotcubes = isop(unary_not(fstar));

  // Step 2 - Create conditions and solve
  
  auto *lp = make_lp( 0, nvars + 1 );

  set_verbose( lp, 1 );
  
  struct _deleter {
    lprec *lp = nullptr;
    ~_deleter() noexcept {
      delete_lp( lp );
    }
  } deleter{ lp };

  for ( auto i = 1u; i <= nvars + 1; ++i )
  {
    set_int( lp, i, TRUE );
  }

  std::vector<REAL> row(nvars + 2, 0);
  row[nvars + 1] = -1; // threshold
  REAL *rowp = &row[0];

  for ( auto &c: fstarcubes )
  {
    for ( auto i = 0u; i < nvars; ++i )
    {
      if ( c.get_mask(i) && c.get_bit(i) )
        row[i + 1] = 1;
      else
        row[i + 1] = 0;
    }

    add_constraint(lp, rowp, GE, 0);
  }

  for ( auto &c: fstarnotcubes )
  {
    for ( auto i = 0u; i < nvars; ++i )
    {
      if ( !c.get_mask(i) || c.get_bit(i) )
        row[i + 1] = 1;
      else
        row[i + 1] = 0;
    }

    add_constraint(lp, rowp, LE, -1);
  }

  for ( auto i = 1u; i <= nvars + 1; ++i )
  {
    row[i] = 1;
  }

  set_obj_fn( lp, rowp );

  if ( solve( lp ) == INFEASIBLE )
    return false;

  if ( plf )
  {
    // Step 3 (optional): Recover the linear form

    REAL *sol;
    get_ptr_variables( lp, &sol );

    for ( auto i = 0u; i < nvars + 1; ++i )
      linear_form[i] = sol[i];
    
    for ( auto i = 0u; i < nvars; ++i )
      if ( negated[i] ) {
        linear_form.back() -= linear_form[i];
        linear_form[i] = -linear_form[i];
      }
    
    plf->swap(linear_form);
  }
  return true;
}

} /* namespace kitty */
