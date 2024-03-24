// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Doubly linked endogenous (intrusive) list
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LIST_H_
#define VERILATOR_V3LIST_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"

#include <type_traits>
#include <utility>

//============================================================================
// The list links (just 2 pointers), to be instantiated as a member in the
// list element base class 'T_Base'. They are considered mutable, even if the
// list element is 'const', as they are only used for storing the elements in
// a V3List. That is, you can store const elements in a V3List.
template <typename T_Base>
class V3ListLinks final {
    T_Base* m_nextp = nullptr;  // Next element in list
    T_Base* m_prevp = nullptr;  // Previous element in list

public:
    V3ListLinks() {
        std::cout << "V3ListLinks cons " << reinterpret_cast<void*>(this) << std::endl;
        std::cout << "  nextp: " << reinterpret_cast<void*>(m_nextp) << std::endl;
        std::cout << "  prevp: " << reinterpret_cast<void*>(m_prevp) << std::endl;
    }
    ~V3ListLinks() {
        std::cout << "func " << __FUNCTION__ << std::endl;

#ifdef VL_DEBUG
        m_nextp = reinterpret_cast<T_Base*>(1);
        m_prevp = reinterpret_cast<T_Base*>(1);
#endif
    }
    VL_UNCOPYABLE(V3ListLinks);
    VL_UNMOVABLE(V3ListLinks);

    T_Base* nextp() const { return m_nextp; }
    void nextp(T_Base* nextp) {
        std::cout << "Setting nextp of " << reinterpret_cast<void*>(this) << " to "
                  << reinterpret_cast<void*>(nextp) << std::endl;
        m_nextp = nextp;
    }
    T_Base* prevp() const { return m_prevp; }
    void prevp(T_Base* prevp) {
        std::cout << "Setting prevp of " << reinterpret_cast<void*>(this) << " to "
                  << reinterpret_cast<void*>(prevp) << std::endl;
        m_prevp = prevp;
    }
};

//============================================================================
// Generic endogenous (or intrusive) doubly linked list, with links stored
// inside the elements. The template parameters are:
// - 'T_Base' is the base type of elements that contains the V3ListLinks
//   instance as a data member.
// - 'LinksPointer' is a member pointer to the links within 'T_Base'
// - 'T_Element' is the actual type of elements, which must be the same,
//    or a subtype of 'T_Base'.
template <typename T_Base, V3ListLinks<T_Base> T_Base::*LinksPointer, typename T_Element = T_Base>
class V3List final {
    static_assert(std::is_base_of<T_Base, T_Element>::value,
                  "'T_Element' must be a subtype of 'T_Base");

    using ListType = V3List<T_Base, LinksPointer, T_Element>;

    // MEMBERS
    T_Base* m_headp = nullptr;
    T_Base* m_lastp = nullptr;

    // Given the T_Base, return the Links. The links are always mutable, even in const elements.
    VL_ATTR_ALWINLINE
    static V3ListLinks<T_Base>& toLinks(const T_Base* elementp) {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return const_cast<T_Base*>(elementp)->*LinksPointer;
    }

    VL_ATTR_ALWINLINE
    static void prefetch(T_Base* elementp, T_Base* fallbackp) {
        std::cout << "func " << __FUNCTION__ << std::endl;
        UDEBUGONLY(UASSERT(fallbackp, "Prefetch fallback pointer must be non nullptr"););
        // This compiles to a branchless prefetch with cmove, with the address always valid
        VL_PREFETCH_RW(elementp ? elementp : fallbackp);
    }

    // Iterator class template for V3List. This is just enough to support range based for loops
    // and basic usage. Feel free to extend as required.
    template <typename T_IteratorElement, bool T_Reverse>
    class SimpleItertatorImpl final {
        static_assert(std::is_same<T_IteratorElement, T_Element>::value
                          || std::is_same<T_IteratorElement, const T_Element>::value,
                      "'SimpleItertatorImpl' must be used with element type only");

        // The List itself, but nothing else can construct iterators
        template <typename B, V3ListLinks<B> B::*P, typename>
        friend class V3List;

        using IteratorType = SimpleItertatorImpl<T_IteratorElement, T_Reverse>;

        T_Base* m_currp;  // Currently iterated element, or 'nullptr' for 'end()' iterator

    public:
        VL_ATTR_ALWINLINE
        SimpleItertatorImpl()
            : m_currp{nullptr} {
            std::cout << "func " << __FUNCTION__ << std::endl;
            std::cout << "SimpleItertatorImpl(): " << reinterpret_cast<void*>(this) << std::endl;
        }

        VL_ATTR_ALWINLINE
        ~SimpleItertatorImpl() {
            std::cout << "func " << __FUNCTION__ << std::endl;
            std::cout << "~SimpleItertatorImpl: " << reinterpret_cast<void*>(this) << std::endl;
        }

        SimpleItertatorImpl(const SimpleItertatorImpl&) = default;
        SimpleItertatorImpl(SimpleItertatorImpl&&) = default;
        SimpleItertatorImpl& operator=(const SimpleItertatorImpl&) = default;
        SimpleItertatorImpl& operator=(SimpleItertatorImpl&&) = default;

    private:
        VL_ATTR_ALWINLINE
        SimpleItertatorImpl(T_Base* elementp)
            : m_currp{elementp} {
            std::cout << "func " << __FUNCTION__ << std::endl;
            std::cout << "SimpleItertatorImpl: " << reinterpret_cast<void*>(this) << std::endl;
        }

        VL_ATTR_ALWINLINE
        static T_Base* step(T_Base* currp) {
            std::cout << "func " << __FUNCTION__ << std::endl;
            if VL_CONSTEXPR_CXX17 (T_Reverse) {
                return toLinks(currp).prevp();
            } else {
                return toLinks(currp).nextp();
            }
        }

    public:
        // Dereference
        VL_ATTR_ALWINLINE
        T_IteratorElement& operator*() const {
            std::cout << "enter " << __FUNCTION__ << std::endl;
            std::cout << "* " << reinterpret_cast<const void*>(this) << std::endl;
            std::cout << "* " << reinterpret_cast<const void*>(m_currp) << std::endl;

            UDEBUGONLY(UASSERT(m_currp, "Dereferencing end of list iterator"););
            prefetch(step(m_currp), m_currp);
            std::cout << "deref " << __FUNCTION__ << std::endl;
            T_IteratorElement& e = *static_cast<T_IteratorElement*>(m_currp);
            std::cout << "exit " << __FUNCTION__ << std::endl;
            return e;
        }
        // Pre increment
        VL_ATTR_ALWINLINE
        IteratorType& operator++() {
            std::cout << "enter " << __FUNCTION__ << std::endl;
            UDEBUGONLY(UASSERT(m_currp, "Pre-incrementing end of list iterator"););
            std::cout << "pre++ A " << reinterpret_cast<const void*>(m_currp) << std::endl;
            auto& links = toLinks(m_currp);
            std::cout << "pre++ next " << reinterpret_cast<const void*>(links.nextp())
                      << std::endl;
            std::cout << "pre++ prev " << reinterpret_cast<const void*>(links.prevp())
                      << std::endl;
            m_currp = step(m_currp);
            std::cout << "pre++ B " << reinterpret_cast<const void*>(m_currp) << std::endl;
            std::cout << "exit " << __FUNCTION__ << std::endl;
            return *this;
        }
        // Post increment
        VL_ATTR_ALWINLINE
        IteratorType operator++(int) {
            std::cout << "enter " << __FUNCTION__ << std::endl;
            UDEBUGONLY(UASSERT(m_currp, "Post-incrementing end of list iterator"););
            T_Base* const elementp = m_currp;
            m_currp = step(m_currp);
            std::cout << "exit " << __FUNCTION__ << std::endl;
            return IteratorType{elementp};
        }
        VL_ATTR_ALWINLINE
        bool operator==(const IteratorType& other) const {
            std::cout << "func " << __FUNCTION__ << std::endl;
            return m_currp == other.m_currp;
        }
        VL_ATTR_ALWINLINE
        bool operator!=(const IteratorType& other) const {
            std::cout << "func " << __FUNCTION__ << std::endl;
            std::cout << "!= 0 " << reinterpret_cast<const void*>(this) << std::endl;
            std::cout << "!= A " << reinterpret_cast<const void*>(m_currp) << std::endl;
            std::cout << "!= B " << reinterpret_cast<const void*>(&other) << std::endl;
            std::cout << "!= C " << reinterpret_cast<const void*>(other.m_currp) << std::endl;
            return m_currp != other.m_currp;
        }
        // Convert to const iterator
        VL_ATTR_ALWINLINE
        operator SimpleItertatorImpl<const T_IteratorElement, T_Reverse>() const {
            std::cout << "func " << __FUNCTION__ << std::endl;

            return SimpleItertatorImpl<const T_IteratorElement, T_Reverse>{m_currp};
        }
    };

    // Proxy class for creating unlinkable iterators, so we can use
    // 'for (T_Element* const ptr : list.unlinkable()) list.unlink(ptr);'
    class UnlinkableProxy final {
        // The List itself, but nothing else can construct Unlinkable
        template <typename B, V3ListLinks<B> B::*P, typename>
        friend class V3List;

        ListType* m_listp;  // The proxied list

        UnlinkableProxy(ListType* listp)
            : m_listp{listp} {}

    public:
        ~UnlinkableProxy() = default;
        UnlinkableProxy(const UnlinkableProxy&) = default;
        UnlinkableProxy(UnlinkableProxy&& that) = default;
        UnlinkableProxy& operator=(const UnlinkableProxy&) = default;
        UnlinkableProxy& operator=(UnlinkableProxy&&) = default;

        // Unlinkable iterator class template. This only supports enough for range based for loops.
        // If you want something fancier, use and manage the direct iterator manually.
        template <typename T_IteratorElement>
        class UnlinkableItertatorImpl final {
            static_assert(std::is_same<T_IteratorElement, T_Element>::value
                              || std::is_same<T_IteratorElement, const T_Element>::value,
                          "'UnlinkableItertatorImpl' must be used with element type only");

            // The UnlinkableProxy, but nothing else can construct unlinkable iterators
            friend class UnlinkableProxy;

            using IteratorType = UnlinkableItertatorImpl<T_IteratorElement>;

            T_Base* m_currp;  // Currently iterated element, or 'nullptr' for 'end()' iterator
            T_Base* m_nextp;  // Next element after current, or 'nullptr' for 'end()' iterator

            VL_ATTR_ALWINLINE
            UnlinkableItertatorImpl(T_Base* elementp)
                : m_currp{elementp}
                , m_nextp{toLinks(m_currp).nextp()} {
                std::cout << "func " << __FUNCTION__ << std::endl;
            }

        public:
            VL_ATTR_ALWINLINE
            UnlinkableItertatorImpl()
                : m_currp{nullptr}
                , m_nextp{nullptr} {
                std::cout << "func " << __FUNCTION__ << std::endl;
            }
            ~UnlinkableItertatorImpl() = default;
            UnlinkableItertatorImpl(const UnlinkableItertatorImpl&) = default;
            UnlinkableItertatorImpl(UnlinkableItertatorImpl&&) = default;
            UnlinkableItertatorImpl& operator=(const UnlinkableItertatorImpl&) = default;
            UnlinkableItertatorImpl& operator=(UnlinkableItertatorImpl&&) = default;

        public:
            // Dereference - Note this returns a pointer.
            VL_ATTR_ALWINLINE
            T_IteratorElement* operator*() const {
                std::cout << "enter " << __FUNCTION__ << std::endl;
                UDEBUGONLY(UASSERT(m_currp, "Dereferencing end of list iterator"););
                prefetch(m_nextp, m_currp);
                std::cout << "exit " << __FUNCTION__ << std::endl;
                return static_cast<T_IteratorElement*>(m_currp);
            }
            // Pre increment - Keeps hold of current next pointer.
            VL_ATTR_ALWINLINE
            IteratorType& operator++() {
                std::cout << "enter " << __FUNCTION__ << std::endl;
                UDEBUGONLY(UASSERT(m_currp, "Pre-incrementing end of list iterator"););
                m_currp = m_nextp;
                m_nextp = m_currp ? toLinks(m_currp).nextp() : nullptr;
                std::cout << "exit " << __FUNCTION__ << std::endl;
                return *this;
            }
            VL_ATTR_ALWINLINE
            bool operator!=(const IteratorType& other) const {
                std::cout << "func " << __FUNCTION__ << std::endl;
                return m_currp != other.m_currp;
            }
        };

    public:
        using iterator = UnlinkableItertatorImpl<T_Element>;
        using const_iterator = UnlinkableItertatorImpl<const T_Element>;
        iterator begin() {  //
            std::cout << "func " << __FUNCTION__ << std::endl;
            return m_listp->m_headp ? iterator{m_listp->m_headp} : end();
        }
        const_iterator begin() const {
            std::cout << "func " << __FUNCTION__ << std::endl;
            return m_listp->m_headp ? const_iterator{m_listp->m_headp} : end();
        }
        iterator end() {
            std::cout << "func " << __FUNCTION__ << std::endl;
            return iterator{};
        }
        const_iterator end() const {
            std::cout << "func " << __FUNCTION__ << std::endl;
            return const_iterator{};
        }
    };

public:
    using iterator = SimpleItertatorImpl<T_Element, /* T_Reverse: */ false>;
    using const_iterator = SimpleItertatorImpl<const T_Element, /* T_Reverse: */ false>;
    using reverse_iterator = SimpleItertatorImpl<T_Element, /* T_Reverse: */ true>;
    using const_reverse_iterator = SimpleItertatorImpl<const T_Element, /* T_Reverse: */ true>;

    static_assert(std::is_default_constructible<iterator>::value, "E");
    static_assert(std::is_default_constructible<const_iterator>::value, "E");
    static_assert(std::is_default_constructible<reverse_iterator>::value, "E");
    static_assert(std::is_default_constructible<const_reverse_iterator>::value, "E");

    // CONSTRUCTOR
    V3List() { std::cout << "func " << __FUNCTION__ << std::endl; }
    ~V3List() {
        std::cout << "func " << __FUNCTION__ << std::endl;
#ifdef VL_DEBUG
        m_headp = reinterpret_cast<T_Element*>(1);
        m_lastp = reinterpret_cast<T_Element*>(1);
#endif
    }
    VL_UNCOPYABLE(V3List);
    VL_UNMOVABLE(V3List);

    // METHDOS
    bool empty() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return !m_headp;
    }
    bool hasSingleElement() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return m_headp && m_headp == m_lastp;
    }
    bool hasMultipleElements() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return m_headp && m_headp != m_lastp;
    }

    // These return pointers, as we often want to unlink/delete them, and can also signal empty
    T_Element* frontp() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return static_cast<T_Element*>(m_headp);
    }
    const T_Element* frontp() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return static_cast<T_Element*>(m_headp);
    }
    T_Element* backp() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return static_cast<T_Element*>(m_lastp);
    }
    const T_Element* backp() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return static_cast<T_Element*>(m_lastp);
    }

    // Standard iterators. The iterator is only invalidated if the element it points to is
    // unlinked. Other list operations do not invalidate the itartor. If you want to be able to
    // unlink the currently iterated element, use 'unlinkable()' below.
    iterator begin() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return iterator{m_headp};
    }
    const_iterator begin() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return const_iterator{m_headp};
    }
    iterator end() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return iterator{nullptr};
    }
    const_iterator end() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return const_iterator{nullptr};
    }
    reverse_iterator rbegin() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return reverse_iterator{m_lastp};
    }
    const_reverse_iterator rbegin() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return const_reverse_iterator{m_lastp};
    }
    reverse_iterator rend() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return reverse_iterator{nullptr};
    }
    const_reverse_iterator rend() const {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return const_reverse_iterator{nullptr};
    }

    // Handle to create unlinkable iterators, which allows unlinking the currently iterated
    // element without invalidating the iterator. However, every other operation that mutates
    // the list invalidates the unlinkable iterator!
    UnlinkableProxy unlinkable() {
        std::cout << "func " << __FUNCTION__ << std::endl;
        return UnlinkableProxy{this};
    }

    // Link (insert) existing element at front
    void linkFront(const T_Element* elementp) {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        auto& links = toLinks(elementp);
        links.nextp(m_headp);
        links.prevp(nullptr);
        if (m_headp) toLinks(m_headp).prevp(const_cast<T_Element*>(elementp));
        m_headp = const_cast<T_Element*>(elementp);
        if (!m_lastp) m_lastp = m_headp;
        std::cout << "exit " << __FUNCTION__ << std::endl;
    }

    // Link (insert) existing element at back
    void linkBack(const T_Element* elementp) {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        auto& links = toLinks(elementp);
        links.nextp(nullptr);
        links.prevp(m_lastp);
        if (m_lastp) toLinks(m_lastp).nextp(const_cast<T_Element*>(elementp));
        m_lastp = const_cast<T_Element*>(elementp);
        if (!m_headp) m_headp = m_lastp;
        std::cout << "exit " << __FUNCTION__ << std::endl;
    }

    // Unlink (remove) and return element at the front. Returns 'nullptr' if the list is empty.
    T_Element* unlinkFront() {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        T_Element* const headp = m_headp;
        if (headp) {
            auto& links = toLinks(headp);
            m_headp = links.nextp();
            links.nextp(nullptr);
            links.prevp(nullptr);
            if (m_headp) {
                toLinks(m_headp).prevp(nullptr);
            } else {
                m_lastp = nullptr;
            }
        }
        std::cout << "exit " << __FUNCTION__ << std::endl;
        return headp;
    }

    // Unlink (remove) and return element at the back. Returns 'nullptr' if the list is empty.
    T_Element* unlinkBack() {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        T_Element* const lastp = m_lastp;
        if (lastp) {
            auto& links = toLinks(lastp);
            m_lastp = links.prevp();
            links.nextp(nullptr);
            links.prevp(nullptr);
            if (m_lastp) {
                toLinks(m_lastp).nextp(nullptr);
            } else {
                m_headp = nullptr;
            }
        }
        std::cout << "exit " << __FUNCTION__ << std::endl;
        return lastp;
    }

    // Unlink (remove) the given element.
    void unlink(const T_Element* elementp) {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        auto& links = toLinks(elementp);
        if (links.nextp()) toLinks(links.nextp()).prevp(links.prevp());
        if (links.prevp()) toLinks(links.prevp()).nextp(links.nextp());
        if (m_headp == elementp) m_headp = links.nextp();
        if (m_lastp == elementp) m_lastp = links.prevp();
        links.prevp(nullptr);
        links.nextp(nullptr);
        std::cout << "exit " << __FUNCTION__ << std::endl;
    }

    // Swap elements of 2 lists
    void swap(ListType& other) {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        std::swap(m_headp, other.m_headp);
        std::swap(m_lastp, other.m_lastp);
        std::cout << "exit " << __FUNCTION__ << std::endl;
    }

    // Take elements from 'other' and link (insert) them all before the given position.
    void splice(const_iterator pos, ListType& other) {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        if (empty()) {
            swap(other);
        } else if (other.empty()) {
            std::cout << "exit " << __FUNCTION__ << std::endl;
            return;
        } else {
            UASSERT(pos == end(), "Sorry, only splicing at the end is implemented at the moment");
            toLinks(m_lastp).nextp(other.m_headp);
            toLinks(other.m_headp).prevp(m_lastp);
            m_lastp = other.m_lastp;
            other.m_headp = nullptr;
            other.m_lastp = nullptr;
        }
        std::cout << "exit " << __FUNCTION__ << std::endl;
    }

    // This is O(n)!
    size_t size() const {
        std::cout << "enter " << __FUNCTION__ << std::endl;
        size_t result = 0;
        for (auto it = begin(); it != end(); ++it) ++result;
        std::cout << "exit " << __FUNCTION__ << std::endl;
        return result;
    }
};

#endif  // Guard
