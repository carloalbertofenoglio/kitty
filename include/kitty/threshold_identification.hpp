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

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include "constructors.hpp"
#include "dynamic_truth_table.hpp"
#include "static_truth_table.hpp"
#include "constructors.hpp"
#include <iostream>
#include "isop.hpp"
#include "cube.hpp"
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"

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
      std::vector<int64_t> linear_form, flipped;
      bool pos_unate, neg_unate;
      TT new_tt = tt;
      std::vector<cube> onset, offset;
      cube new_cube;
      lprec* lp;
      int Ncol, *colno = NULL, j, ret = 0;
      REAL* row = NULL;

      /* TODO */
      /* if tt is non-TF: */
      for ( auto i = 0u; i < tt.num_vars(); ++i )
      {
        pos_unate = implies( cofactor0( tt, i ), cofactor1( tt, i ) );
        neg_unate = implies( cofactor1( tt, i ), cofactor0( tt, i ) );

        if ( pos_unate )
        {
          flipped.emplace_back( 0 ); /* var wasn't flipped*/
                                     // std::cout << "La funzione e' positive unate nella variabile " << i << std:: endl;
        }
        else if ( neg_unate )
        {
          flip_inplace( new_tt, i ); /*update tt*/
          flipped.emplace_back( 1 ); /*var was flipped*/
                                     // std:: cout <<" La funzione e' positive unate nella variabile " << i << std:: endl;
        }
        else
          return false;
      }
      //for ( auto i = 0u; i < tt.num_vars(); ++i)
      //{
      //  std::cout << flipped[i] << std::endl;   /*print flipped to check*/
      //}

      /* if tt is TF: */
      onset = isop( new_tt );
      offset = isop( unary_not( new_tt ) );

      /*for (auto &i : onset)
      {
          std::cout << "Le vaiabili contenute nei cubi dell' onset sono" << std::endl;
          for (auto j = 0u; j < tt.num_vars(); ++j)
          {
              new_cube = i;
              new_cube.remove_literal(j);
          
              if (new_cube.num_literals() != i.num_literals())
              {
                 std:: cout << j << std::endl;
              }
          }
      }*/


      /* We will build the model row by row
         So we start with creating a model with 0 rows and num_vars + 1 columns */
      Ncol = tt.num_vars() + 1; /* the variables in the model */
      lp = make_lp( 0, Ncol );
      if ( lp == NULL )
        ret = 1; /* couldn't construct a new model... */

       if (ret == 0) {

      /* create space large enough for one row */
      colno = (int*)malloc( Ncol * sizeof( *colno ) );
      row = (REAL*)malloc( Ncol * sizeof( *row ) );

      if ( ( colno == NULL ) || ( row == NULL ) )
        ret = 2;

        set_add_rowmode( lp, TRUE ); /* makes building the model faster if it is done rows by row */

        /* construct rows for onset */
        for ( auto& i : onset )
        {
          //std::cout << "Le variabili contenute nei cubi dell' onset sono" << std::endl; /* useful for check*/
          for ( auto j = 0u; j < tt.num_vars(); ++j )
          {
            new_cube = i;
            new_cube.remove_literal( j );

            if ( new_cube.num_literals() != i.num_literals() ) /*if the new cube is != from original one it means that the literal was contained in it before removal
                                                                   so it must be taken into account for the constraint*/
            {
              // std::cout << j << std::endl; /*print literals contained in the cube for check*/
              colno[j] = j + 1;
              row[j] = 1;
            }
            else
            {
              colno[j] = j + 1;
              row[j] = 0;
            }
          }
          /*col for threshold*/
          colno[tt.num_vars()] = tt.num_vars() + 1;
          row[tt.num_vars()] = -1;
          /* add the row to lpsolve */
          if ( !add_constraintex( lp, Ncol, row, colno, GE, 0 ) )
            ret = 3;
        }

        /* construct rows for offset */
        for ( auto& i : offset )
        {
          //std::cout << "Le vaiabili contenute nei cubi dell' offset sono" << std::endl; /* useful for check*/
          for ( auto j = 0u; j < tt.num_vars(); ++j )
          {
            new_cube = i;
            new_cube.remove_literal( j );

            if ( new_cube.num_literals() == i.num_literals() ) /*if the new cube is = from original one it means that the literal wasn't contained in it before removal
                                                                so it must be taken into account for the constraint*/
            {
              // std::cout << j << std::endl; /*print literals contained in the cube for check*/
              colno[j] = j + 1;
              row[j] = 1;
            }
            else
            {
              colno[j] = j + 1;
              row[j] = 0;
            }
          }
          /*col for threshold*/
          colno[tt.num_vars()] = tt.num_vars() + 1;
          row[tt.num_vars()] = -1;
          /* add the row to lpsolve */
          if ( !add_constraintex( lp, Ncol, row, colno, LE, -1 ) )
            ret = 3;
        }

        /* constraints on single vars and T to be GE 0*/
        for ( auto j = 0u; j < Ncol; ++j )
        {
          for (auto h = 0u; h < Ncol; ++h)
          {
            if (j == h) 
            {
              colno[j] = j + 1;
              row[j] = 1;
            }
            else 
            {
              colno[h] = h + 1;
              row[h] = 0;
            }
          }
          /* add the row to lpsolve */
          if ( !add_constraintex( lp, Ncol, row, colno, GE, 0 ) )
            ret = 3;
        }

        set_add_rowmode( lp, FALSE ); /* rowmode should be turned off again when done building the model */

        /* set the objective function : min(sum(w_i) + T) */
        for ( auto j = 0u; j < Ncol; ++j )
        {
          colno[j] = j + 1;
          row[j] = 1;
          /* add the row to lpsolve */
        }

        /* set the objective in lpsolve */
        if ( !set_obj_fnex( lp, Ncol, row, colno ) )
          ret = 4;

        /* set the object direction to minimize */
        set_minim( lp );

        /* just out of curiousity, now show the model in lp format on screen */
        //write_LP( lp, stdout );

        /* I only want to see important messages on screen while solving */
        set_verbose( lp, IMPORTANT );

        /* Now let lpsolve calculate a solution */
        ret = solve( lp );
   
        /* a solution is calculated, now lets get some results */

        /* objective value */
        //printf( "Objective value: %f\n", get_objective( lp ) );

        /* variable values */
        get_variables( lp, row );
        //for ( j = 0; j < Ncol; j++ )
        //{
        //  printf( "%s: %f\n", get_col_name( lp, j + 1 ), row[j] );
        //}

        /*let's populate linear_form*/
        for (  j = 0; j < Ncol-1; j++ ) /*flipped.size = Ncol - 1 = num_vars*/
        {
          if ( flipped[j] == 0 )
          {
            linear_form.emplace_back( row[j] ); /* save w_j as it is*/
          }
          else
          {
            linear_form.emplace_back( -row[j] );    /*save w_j flipped */
            row[Ncol - 1] = row[Ncol - 1] - row[j]; /* and subtract w_j to T ( see pdf)*/
          }
        }
        linear_form.emplace_back( row[Ncol - 1] ); /* add T - w_j i.e. last term of linear form*/

        /*check linear form*/
       /* for (  j = 0; j < linear_form.size(); j++ )
        {
          std::cout << "linear form is --> " << linear_form.at( j ) << std::endl;
          std::cout << "row: --> " << (int)row[j] << std::endl;
        }*/
        /* we are done now */
      }
  
      /* free allocated memory */
      if ( row != NULL )
        free( row );
      if ( colno != NULL )
        free( colno );

      if ( lp != NULL )
      {
        /* clean up such that all used memory by lpsolve is freed */
        delete_lp( lp );
      }
      if ( ret != OPTIMAL )
        return false;
      /* push the weight and threshold values into `linear_form` */
      if ( plf )
      {
        *plf = linear_form;
      }
      return true;
    }
} /* namespace kitty */
